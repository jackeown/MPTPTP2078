%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:23 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  246 (3178 expanded)
%              Number of clauses        :  143 ( 783 expanded)
%              Number of leaves         :   26 (1092 expanded)
%              Depth                    :   23
%              Number of atoms          : 1235 (33235 expanded)
%              Number of equality atoms :  432 (7471 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4
          | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK6,X3,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5
              | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK5,X2,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4
                  | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
                & v1_funct_2(X5,sK4,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
                    ( ( k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4
                      | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
                & v1_funct_2(X4,sK3,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK3,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2)))
                        & v1_funct_2(X5,X3,sK2)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
                    & v1_funct_2(X4,X2,sK2)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
                          ( ( k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK1))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK1))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_2(sK6,sK4,sK2)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & r1_subset_1(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & ~ v1_xboole_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f48,f64,f63,f62,f61,f60,f59])).

fof(f110,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f3,axiom,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

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
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f103,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f65])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f108,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f111,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f65])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f104,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f100,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f106,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f98,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f101,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f18,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f117,plain,(
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
    inference(equality_resolution,[],[f93])).

fof(f19,axiom,(
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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f109,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f118,plain,(
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
    inference(equality_resolution,[],[f92])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2292,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_20,c_16])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_621,c_20,c_19,c_16])).

cnf(c_2274,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_3489,plain,
    ( k7_relat_1(sK6,sK4) = sK6 ),
    inference(superposition,[status(thm)],[c_2292,c_2274])).

cnf(c_2298,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4003,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_2298])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2308,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2303,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2306,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_344,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_345,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_344])).

cnf(c_436,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_345])).

cnf(c_2276,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_4067,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X2,X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2306,c_2276])).

cnf(c_8111,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2303,c_4067])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2309,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8214,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8111,c_2309])).

cnf(c_8219,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2308,c_8214])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2310,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8640,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8219,c_2310])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2299,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8671,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8640,c_2299])).

cnf(c_8713,plain,
    ( k7_relat_1(k7_relat_1(sK6,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4003,c_8671])).

cnf(c_8757,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3489,c_8713])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2286,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2301,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3592,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2286,c_2301])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_432,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_345])).

cnf(c_2278,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_7319,plain,
    ( k9_subset_1(sK1,X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_3592,c_2278])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2289,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2297,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4343,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_2297])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_53,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4918,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4343,c_53])).

cnf(c_4342,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_2297])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_56,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4846,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4342,c_56])).

cnf(c_32,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4849,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_4846,c_32])).

cnf(c_4921,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_4918,c_4849])).

cnf(c_7425,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_7319,c_4921])).

cnf(c_18,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_588,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_589,plain,
    ( r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_591,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_43,c_41])).

cnf(c_2275,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_3405,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2275,c_2309])).

cnf(c_4004,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_2298])).

cnf(c_4167,plain,
    ( k7_relat_1(k7_relat_1(X0,sK3),sK4) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_2299])).

cnf(c_4266,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4004,c_4167])).

cnf(c_3490,plain,
    ( k7_relat_1(sK5,sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_2289,c_2274])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2300,plain,
    ( k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4170,plain,
    ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0)) = k7_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_4004,c_2300])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_24,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_601,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_20,c_24])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_601,c_24,c_20,c_19])).

cnf(c_606,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_605])).

cnf(c_696,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_21,c_606])).

cnf(c_700,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_696,c_24,c_21,c_20,c_19])).

cnf(c_701,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_700])).

cnf(c_2273,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_3208,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_2273])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2476,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK2)
    | k1_relat_1(X0) = X1 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_2685,plain,
    ( ~ v1_funct_2(sK5,X0,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | k1_relat_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_2476])).

cnf(c_2687,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_3311,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3208,c_44,c_38,c_37,c_36,c_2687])).

cnf(c_4171,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK3,X0)) = k7_relat_1(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_4170,c_3311])).

cnf(c_4210,plain,
    ( k7_relat_1(sK5,sK4) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3405,c_4171])).

cnf(c_4267,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4266,c_3490,c_4210])).

cnf(c_7426,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7425,c_3405,c_4267])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f117])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f95])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f96])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f97])).

cnf(c_255,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_31,c_30,c_29])).

cnf(c_256,plain,
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
    inference(renaming,[status(thm)],[c_255])).

cnf(c_2279,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
    | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X5,X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_6774,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4846,c_2279])).

cnf(c_47,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_50,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_57,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_58,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6898,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6774,c_47,c_50,c_56,c_57,c_58])).

cnf(c_6899,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6898])).

cnf(c_6905,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4918,c_6899])).

cnf(c_48,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_54,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_55,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7027,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6905,c_48,c_53,c_54,c_55])).

cnf(c_7028,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7027])).

cnf(c_7434,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7319,c_7028])).

cnf(c_7435,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7434,c_3405])).

cnf(c_7436,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7435,c_4171,c_7319])).

cnf(c_7437,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7436,c_4210,c_4267])).

cnf(c_7445,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7437])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f118])).

cnf(c_248,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_31,c_30,c_29])).

cnf(c_249,plain,
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
    inference(renaming,[status(thm)],[c_248])).

cnf(c_2280,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
    | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X5,X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_7147,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4846,c_2280])).

cnf(c_7902,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7147,c_47,c_50,c_56,c_57,c_58])).

cnf(c_7903,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7902])).

cnf(c_7909,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4918,c_7903])).

cnf(c_7949,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7909,c_48,c_53,c_54,c_55])).

cnf(c_7950,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7949])).

cnf(c_7955,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7319,c_7950])).

cnf(c_7960,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7955,c_3405])).

cnf(c_7961,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7960,c_4171,c_7319])).

cnf(c_7962,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7961,c_4210,c_4267])).

cnf(c_7964,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7962])).

cnf(c_8525,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7426,c_45,c_42,c_40,c_7445,c_7964])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8757,c_8525])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.67/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.04  
% 3.67/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/1.04  
% 3.67/1.04  ------  iProver source info
% 3.67/1.04  
% 3.67/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.67/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/1.04  git: non_committed_changes: false
% 3.67/1.04  git: last_make_outside_of_git: false
% 3.67/1.04  
% 3.67/1.04  ------ 
% 3.67/1.04  
% 3.67/1.04  ------ Input Options
% 3.67/1.04  
% 3.67/1.04  --out_options                           all
% 3.67/1.04  --tptp_safe_out                         true
% 3.67/1.04  --problem_path                          ""
% 3.67/1.04  --include_path                          ""
% 3.67/1.04  --clausifier                            res/vclausify_rel
% 3.67/1.04  --clausifier_options                    ""
% 3.67/1.04  --stdin                                 false
% 3.67/1.04  --stats_out                             all
% 3.67/1.04  
% 3.67/1.04  ------ General Options
% 3.67/1.04  
% 3.67/1.04  --fof                                   false
% 3.67/1.04  --time_out_real                         305.
% 3.67/1.04  --time_out_virtual                      -1.
% 3.67/1.04  --symbol_type_check                     false
% 3.67/1.04  --clausify_out                          false
% 3.67/1.04  --sig_cnt_out                           false
% 3.67/1.04  --trig_cnt_out                          false
% 3.67/1.04  --trig_cnt_out_tolerance                1.
% 3.67/1.04  --trig_cnt_out_sk_spl                   false
% 3.67/1.04  --abstr_cl_out                          false
% 3.67/1.04  
% 3.67/1.04  ------ Global Options
% 3.67/1.04  
% 3.67/1.04  --schedule                              default
% 3.67/1.04  --add_important_lit                     false
% 3.67/1.04  --prop_solver_per_cl                    1000
% 3.67/1.04  --min_unsat_core                        false
% 3.67/1.04  --soft_assumptions                      false
% 3.67/1.04  --soft_lemma_size                       3
% 3.67/1.04  --prop_impl_unit_size                   0
% 3.67/1.04  --prop_impl_unit                        []
% 3.67/1.04  --share_sel_clauses                     true
% 3.67/1.04  --reset_solvers                         false
% 3.67/1.04  --bc_imp_inh                            [conj_cone]
% 3.67/1.04  --conj_cone_tolerance                   3.
% 3.67/1.04  --extra_neg_conj                        none
% 3.67/1.04  --large_theory_mode                     true
% 3.67/1.04  --prolific_symb_bound                   200
% 3.67/1.04  --lt_threshold                          2000
% 3.67/1.04  --clause_weak_htbl                      true
% 3.67/1.04  --gc_record_bc_elim                     false
% 3.67/1.04  
% 3.67/1.04  ------ Preprocessing Options
% 3.67/1.04  
% 3.67/1.04  --preprocessing_flag                    true
% 3.67/1.04  --time_out_prep_mult                    0.1
% 3.67/1.04  --splitting_mode                        input
% 3.67/1.04  --splitting_grd                         true
% 3.67/1.04  --splitting_cvd                         false
% 3.67/1.04  --splitting_cvd_svl                     false
% 3.67/1.04  --splitting_nvd                         32
% 3.67/1.04  --sub_typing                            true
% 3.67/1.04  --prep_gs_sim                           true
% 3.67/1.04  --prep_unflatten                        true
% 3.67/1.04  --prep_res_sim                          true
% 3.67/1.04  --prep_upred                            true
% 3.67/1.04  --prep_sem_filter                       exhaustive
% 3.67/1.04  --prep_sem_filter_out                   false
% 3.67/1.04  --pred_elim                             true
% 3.67/1.04  --res_sim_input                         true
% 3.67/1.04  --eq_ax_congr_red                       true
% 3.67/1.04  --pure_diseq_elim                       true
% 3.67/1.04  --brand_transform                       false
% 3.67/1.04  --non_eq_to_eq                          false
% 3.67/1.04  --prep_def_merge                        true
% 3.67/1.04  --prep_def_merge_prop_impl              false
% 3.67/1.04  --prep_def_merge_mbd                    true
% 3.67/1.04  --prep_def_merge_tr_red                 false
% 3.67/1.04  --prep_def_merge_tr_cl                  false
% 3.67/1.04  --smt_preprocessing                     true
% 3.67/1.04  --smt_ac_axioms                         fast
% 3.67/1.04  --preprocessed_out                      false
% 3.67/1.04  --preprocessed_stats                    false
% 3.67/1.04  
% 3.67/1.04  ------ Abstraction refinement Options
% 3.67/1.04  
% 3.67/1.04  --abstr_ref                             []
% 3.67/1.04  --abstr_ref_prep                        false
% 3.67/1.04  --abstr_ref_until_sat                   false
% 3.67/1.04  --abstr_ref_sig_restrict                funpre
% 3.67/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.04  --abstr_ref_under                       []
% 3.67/1.04  
% 3.67/1.04  ------ SAT Options
% 3.67/1.04  
% 3.67/1.04  --sat_mode                              false
% 3.67/1.04  --sat_fm_restart_options                ""
% 3.67/1.04  --sat_gr_def                            false
% 3.67/1.04  --sat_epr_types                         true
% 3.67/1.04  --sat_non_cyclic_types                  false
% 3.67/1.04  --sat_finite_models                     false
% 3.67/1.04  --sat_fm_lemmas                         false
% 3.67/1.04  --sat_fm_prep                           false
% 3.67/1.04  --sat_fm_uc_incr                        true
% 3.67/1.04  --sat_out_model                         small
% 3.67/1.04  --sat_out_clauses                       false
% 3.67/1.04  
% 3.67/1.04  ------ QBF Options
% 3.67/1.04  
% 3.67/1.04  --qbf_mode                              false
% 3.67/1.04  --qbf_elim_univ                         false
% 3.67/1.04  --qbf_dom_inst                          none
% 3.67/1.04  --qbf_dom_pre_inst                      false
% 3.67/1.04  --qbf_sk_in                             false
% 3.67/1.04  --qbf_pred_elim                         true
% 3.67/1.04  --qbf_split                             512
% 3.67/1.04  
% 3.67/1.04  ------ BMC1 Options
% 3.67/1.04  
% 3.67/1.04  --bmc1_incremental                      false
% 3.67/1.04  --bmc1_axioms                           reachable_all
% 3.67/1.04  --bmc1_min_bound                        0
% 3.67/1.04  --bmc1_max_bound                        -1
% 3.67/1.04  --bmc1_max_bound_default                -1
% 3.67/1.04  --bmc1_symbol_reachability              true
% 3.67/1.04  --bmc1_property_lemmas                  false
% 3.67/1.04  --bmc1_k_induction                      false
% 3.67/1.04  --bmc1_non_equiv_states                 false
% 3.67/1.04  --bmc1_deadlock                         false
% 3.67/1.04  --bmc1_ucm                              false
% 3.67/1.04  --bmc1_add_unsat_core                   none
% 3.67/1.04  --bmc1_unsat_core_children              false
% 3.67/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.04  --bmc1_out_stat                         full
% 3.67/1.04  --bmc1_ground_init                      false
% 3.67/1.04  --bmc1_pre_inst_next_state              false
% 3.67/1.04  --bmc1_pre_inst_state                   false
% 3.67/1.04  --bmc1_pre_inst_reach_state             false
% 3.67/1.04  --bmc1_out_unsat_core                   false
% 3.67/1.04  --bmc1_aig_witness_out                  false
% 3.67/1.04  --bmc1_verbose                          false
% 3.67/1.04  --bmc1_dump_clauses_tptp                false
% 3.67/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.04  --bmc1_dump_file                        -
% 3.67/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.04  --bmc1_ucm_extend_mode                  1
% 3.67/1.04  --bmc1_ucm_init_mode                    2
% 3.67/1.04  --bmc1_ucm_cone_mode                    none
% 3.67/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.04  --bmc1_ucm_relax_model                  4
% 3.67/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.04  --bmc1_ucm_layered_model                none
% 3.67/1.04  --bmc1_ucm_max_lemma_size               10
% 3.67/1.04  
% 3.67/1.04  ------ AIG Options
% 3.67/1.04  
% 3.67/1.04  --aig_mode                              false
% 3.67/1.04  
% 3.67/1.04  ------ Instantiation Options
% 3.67/1.04  
% 3.67/1.04  --instantiation_flag                    true
% 3.67/1.04  --inst_sos_flag                         true
% 3.67/1.04  --inst_sos_phase                        true
% 3.67/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.04  --inst_lit_sel_side                     num_symb
% 3.67/1.04  --inst_solver_per_active                1400
% 3.67/1.04  --inst_solver_calls_frac                1.
% 3.67/1.04  --inst_passive_queue_type               priority_queues
% 3.67/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.04  --inst_passive_queues_freq              [25;2]
% 3.67/1.04  --inst_dismatching                      true
% 3.67/1.04  --inst_eager_unprocessed_to_passive     true
% 3.67/1.04  --inst_prop_sim_given                   true
% 3.67/1.04  --inst_prop_sim_new                     false
% 3.67/1.04  --inst_subs_new                         false
% 3.67/1.04  --inst_eq_res_simp                      false
% 3.67/1.04  --inst_subs_given                       false
% 3.67/1.04  --inst_orphan_elimination               true
% 3.67/1.04  --inst_learning_loop_flag               true
% 3.67/1.04  --inst_learning_start                   3000
% 3.67/1.04  --inst_learning_factor                  2
% 3.67/1.04  --inst_start_prop_sim_after_learn       3
% 3.67/1.04  --inst_sel_renew                        solver
% 3.67/1.04  --inst_lit_activity_flag                true
% 3.67/1.04  --inst_restr_to_given                   false
% 3.67/1.04  --inst_activity_threshold               500
% 3.67/1.04  --inst_out_proof                        true
% 3.67/1.04  
% 3.67/1.04  ------ Resolution Options
% 3.67/1.04  
% 3.67/1.04  --resolution_flag                       true
% 3.67/1.04  --res_lit_sel                           adaptive
% 3.67/1.04  --res_lit_sel_side                      none
% 3.67/1.04  --res_ordering                          kbo
% 3.67/1.04  --res_to_prop_solver                    active
% 3.67/1.04  --res_prop_simpl_new                    false
% 3.67/1.04  --res_prop_simpl_given                  true
% 3.67/1.04  --res_passive_queue_type                priority_queues
% 3.67/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.04  --res_passive_queues_freq               [15;5]
% 3.67/1.04  --res_forward_subs                      full
% 3.67/1.04  --res_backward_subs                     full
% 3.67/1.04  --res_forward_subs_resolution           true
% 3.67/1.04  --res_backward_subs_resolution          true
% 3.67/1.04  --res_orphan_elimination                true
% 3.67/1.04  --res_time_limit                        2.
% 3.67/1.04  --res_out_proof                         true
% 3.67/1.04  
% 3.67/1.04  ------ Superposition Options
% 3.67/1.04  
% 3.67/1.04  --superposition_flag                    true
% 3.67/1.04  --sup_passive_queue_type                priority_queues
% 3.67/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.67/1.04  --demod_completeness_check              fast
% 3.67/1.04  --demod_use_ground                      true
% 3.67/1.04  --sup_to_prop_solver                    passive
% 3.67/1.04  --sup_prop_simpl_new                    true
% 3.67/1.04  --sup_prop_simpl_given                  true
% 3.67/1.04  --sup_fun_splitting                     true
% 3.67/1.04  --sup_smt_interval                      50000
% 3.67/1.04  
% 3.67/1.04  ------ Superposition Simplification Setup
% 3.67/1.04  
% 3.67/1.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/1.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/1.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/1.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/1.04  --sup_immed_triv                        [TrivRules]
% 3.67/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.04  --sup_immed_bw_main                     []
% 3.67/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.04  --sup_input_bw                          []
% 3.67/1.04  
% 3.67/1.04  ------ Combination Options
% 3.67/1.04  
% 3.67/1.04  --comb_res_mult                         3
% 3.67/1.04  --comb_sup_mult                         2
% 3.67/1.04  --comb_inst_mult                        10
% 3.67/1.04  
% 3.67/1.04  ------ Debug Options
% 3.67/1.04  
% 3.67/1.04  --dbg_backtrace                         false
% 3.67/1.04  --dbg_dump_prop_clauses                 false
% 3.67/1.04  --dbg_dump_prop_clauses_file            -
% 3.67/1.04  --dbg_out_stat                          false
% 3.67/1.04  ------ Parsing...
% 3.67/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/1.04  
% 3.67/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.67/1.04  
% 3.67/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/1.04  
% 3.67/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/1.04  ------ Proving...
% 3.67/1.04  ------ Problem Properties 
% 3.67/1.04  
% 3.67/1.04  
% 3.67/1.04  clauses                                 39
% 3.67/1.04  conjectures                             13
% 3.67/1.04  EPR                                     15
% 3.67/1.04  Horn                                    30
% 3.67/1.04  unary                                   15
% 3.67/1.04  binary                                  10
% 3.67/1.04  lits                                    145
% 3.67/1.04  lits eq                                 18
% 3.67/1.04  fd_pure                                 0
% 3.67/1.04  fd_pseudo                               0
% 3.67/1.04  fd_cond                                 0
% 3.67/1.04  fd_pseudo_cond                          2
% 3.67/1.04  AC symbols                              0
% 3.67/1.04  
% 3.67/1.04  ------ Schedule dynamic 5 is on 
% 3.67/1.04  
% 3.67/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/1.04  
% 3.67/1.04  
% 3.67/1.04  ------ 
% 3.67/1.04  Current options:
% 3.67/1.04  ------ 
% 3.67/1.04  
% 3.67/1.04  ------ Input Options
% 3.67/1.04  
% 3.67/1.04  --out_options                           all
% 3.67/1.04  --tptp_safe_out                         true
% 3.67/1.04  --problem_path                          ""
% 3.67/1.04  --include_path                          ""
% 3.67/1.04  --clausifier                            res/vclausify_rel
% 3.67/1.04  --clausifier_options                    ""
% 3.67/1.04  --stdin                                 false
% 3.67/1.04  --stats_out                             all
% 3.67/1.04  
% 3.67/1.04  ------ General Options
% 3.67/1.04  
% 3.67/1.04  --fof                                   false
% 3.67/1.04  --time_out_real                         305.
% 3.67/1.04  --time_out_virtual                      -1.
% 3.67/1.04  --symbol_type_check                     false
% 3.67/1.04  --clausify_out                          false
% 3.67/1.04  --sig_cnt_out                           false
% 3.67/1.04  --trig_cnt_out                          false
% 3.67/1.04  --trig_cnt_out_tolerance                1.
% 3.67/1.04  --trig_cnt_out_sk_spl                   false
% 3.67/1.04  --abstr_cl_out                          false
% 3.67/1.04  
% 3.67/1.04  ------ Global Options
% 3.67/1.04  
% 3.67/1.04  --schedule                              default
% 3.67/1.04  --add_important_lit                     false
% 3.67/1.04  --prop_solver_per_cl                    1000
% 3.67/1.04  --min_unsat_core                        false
% 3.67/1.04  --soft_assumptions                      false
% 3.67/1.04  --soft_lemma_size                       3
% 3.67/1.04  --prop_impl_unit_size                   0
% 3.67/1.04  --prop_impl_unit                        []
% 3.67/1.04  --share_sel_clauses                     true
% 3.67/1.04  --reset_solvers                         false
% 3.67/1.04  --bc_imp_inh                            [conj_cone]
% 3.67/1.04  --conj_cone_tolerance                   3.
% 3.67/1.04  --extra_neg_conj                        none
% 3.67/1.04  --large_theory_mode                     true
% 3.67/1.04  --prolific_symb_bound                   200
% 3.67/1.04  --lt_threshold                          2000
% 3.67/1.04  --clause_weak_htbl                      true
% 3.67/1.04  --gc_record_bc_elim                     false
% 3.67/1.04  
% 3.67/1.04  ------ Preprocessing Options
% 3.67/1.04  
% 3.67/1.04  --preprocessing_flag                    true
% 3.67/1.04  --time_out_prep_mult                    0.1
% 3.67/1.04  --splitting_mode                        input
% 3.67/1.04  --splitting_grd                         true
% 3.67/1.04  --splitting_cvd                         false
% 3.67/1.04  --splitting_cvd_svl                     false
% 3.67/1.04  --splitting_nvd                         32
% 3.67/1.04  --sub_typing                            true
% 3.67/1.04  --prep_gs_sim                           true
% 3.67/1.04  --prep_unflatten                        true
% 3.67/1.04  --prep_res_sim                          true
% 3.67/1.04  --prep_upred                            true
% 3.67/1.04  --prep_sem_filter                       exhaustive
% 3.67/1.04  --prep_sem_filter_out                   false
% 3.67/1.04  --pred_elim                             true
% 3.67/1.04  --res_sim_input                         true
% 3.67/1.04  --eq_ax_congr_red                       true
% 3.67/1.04  --pure_diseq_elim                       true
% 3.67/1.04  --brand_transform                       false
% 3.67/1.04  --non_eq_to_eq                          false
% 3.67/1.04  --prep_def_merge                        true
% 3.67/1.04  --prep_def_merge_prop_impl              false
% 3.67/1.04  --prep_def_merge_mbd                    true
% 3.67/1.04  --prep_def_merge_tr_red                 false
% 3.67/1.04  --prep_def_merge_tr_cl                  false
% 3.67/1.04  --smt_preprocessing                     true
% 3.67/1.04  --smt_ac_axioms                         fast
% 3.67/1.04  --preprocessed_out                      false
% 3.67/1.04  --preprocessed_stats                    false
% 3.67/1.04  
% 3.67/1.04  ------ Abstraction refinement Options
% 3.67/1.04  
% 3.67/1.04  --abstr_ref                             []
% 3.67/1.04  --abstr_ref_prep                        false
% 3.67/1.04  --abstr_ref_until_sat                   false
% 3.67/1.04  --abstr_ref_sig_restrict                funpre
% 3.67/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.04  --abstr_ref_under                       []
% 3.67/1.04  
% 3.67/1.04  ------ SAT Options
% 3.67/1.04  
% 3.67/1.04  --sat_mode                              false
% 3.67/1.04  --sat_fm_restart_options                ""
% 3.67/1.04  --sat_gr_def                            false
% 3.67/1.04  --sat_epr_types                         true
% 3.67/1.04  --sat_non_cyclic_types                  false
% 3.67/1.04  --sat_finite_models                     false
% 3.67/1.04  --sat_fm_lemmas                         false
% 3.67/1.04  --sat_fm_prep                           false
% 3.67/1.04  --sat_fm_uc_incr                        true
% 3.67/1.04  --sat_out_model                         small
% 3.67/1.04  --sat_out_clauses                       false
% 3.67/1.04  
% 3.67/1.04  ------ QBF Options
% 3.67/1.04  
% 3.67/1.04  --qbf_mode                              false
% 3.67/1.04  --qbf_elim_univ                         false
% 3.67/1.04  --qbf_dom_inst                          none
% 3.67/1.04  --qbf_dom_pre_inst                      false
% 3.67/1.04  --qbf_sk_in                             false
% 3.67/1.04  --qbf_pred_elim                         true
% 3.67/1.04  --qbf_split                             512
% 3.67/1.04  
% 3.67/1.04  ------ BMC1 Options
% 3.67/1.04  
% 3.67/1.04  --bmc1_incremental                      false
% 3.67/1.04  --bmc1_axioms                           reachable_all
% 3.67/1.04  --bmc1_min_bound                        0
% 3.67/1.04  --bmc1_max_bound                        -1
% 3.67/1.04  --bmc1_max_bound_default                -1
% 3.67/1.04  --bmc1_symbol_reachability              true
% 3.67/1.04  --bmc1_property_lemmas                  false
% 3.67/1.04  --bmc1_k_induction                      false
% 3.67/1.04  --bmc1_non_equiv_states                 false
% 3.67/1.04  --bmc1_deadlock                         false
% 3.67/1.04  --bmc1_ucm                              false
% 3.67/1.04  --bmc1_add_unsat_core                   none
% 3.67/1.04  --bmc1_unsat_core_children              false
% 3.67/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.04  --bmc1_out_stat                         full
% 3.67/1.04  --bmc1_ground_init                      false
% 3.67/1.04  --bmc1_pre_inst_next_state              false
% 3.67/1.04  --bmc1_pre_inst_state                   false
% 3.67/1.04  --bmc1_pre_inst_reach_state             false
% 3.67/1.04  --bmc1_out_unsat_core                   false
% 3.67/1.04  --bmc1_aig_witness_out                  false
% 3.67/1.04  --bmc1_verbose                          false
% 3.67/1.04  --bmc1_dump_clauses_tptp                false
% 3.67/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.04  --bmc1_dump_file                        -
% 3.67/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.04  --bmc1_ucm_extend_mode                  1
% 3.67/1.04  --bmc1_ucm_init_mode                    2
% 3.67/1.04  --bmc1_ucm_cone_mode                    none
% 3.67/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.04  --bmc1_ucm_relax_model                  4
% 3.67/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.04  --bmc1_ucm_layered_model                none
% 3.67/1.04  --bmc1_ucm_max_lemma_size               10
% 3.67/1.04  
% 3.67/1.04  ------ AIG Options
% 3.67/1.04  
% 3.67/1.04  --aig_mode                              false
% 3.67/1.04  
% 3.67/1.04  ------ Instantiation Options
% 3.67/1.04  
% 3.67/1.04  --instantiation_flag                    true
% 3.67/1.04  --inst_sos_flag                         true
% 3.67/1.04  --inst_sos_phase                        true
% 3.67/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.04  --inst_lit_sel_side                     none
% 3.67/1.04  --inst_solver_per_active                1400
% 3.67/1.04  --inst_solver_calls_frac                1.
% 3.67/1.04  --inst_passive_queue_type               priority_queues
% 3.67/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.04  --inst_passive_queues_freq              [25;2]
% 3.67/1.04  --inst_dismatching                      true
% 3.67/1.04  --inst_eager_unprocessed_to_passive     true
% 3.67/1.04  --inst_prop_sim_given                   true
% 3.67/1.04  --inst_prop_sim_new                     false
% 3.67/1.04  --inst_subs_new                         false
% 3.67/1.04  --inst_eq_res_simp                      false
% 3.67/1.04  --inst_subs_given                       false
% 3.67/1.04  --inst_orphan_elimination               true
% 3.67/1.04  --inst_learning_loop_flag               true
% 3.67/1.04  --inst_learning_start                   3000
% 3.67/1.04  --inst_learning_factor                  2
% 3.67/1.04  --inst_start_prop_sim_after_learn       3
% 3.67/1.04  --inst_sel_renew                        solver
% 3.67/1.04  --inst_lit_activity_flag                true
% 3.67/1.04  --inst_restr_to_given                   false
% 3.67/1.04  --inst_activity_threshold               500
% 3.67/1.04  --inst_out_proof                        true
% 3.67/1.04  
% 3.67/1.04  ------ Resolution Options
% 3.67/1.04  
% 3.67/1.04  --resolution_flag                       false
% 3.67/1.04  --res_lit_sel                           adaptive
% 3.67/1.04  --res_lit_sel_side                      none
% 3.67/1.04  --res_ordering                          kbo
% 3.67/1.04  --res_to_prop_solver                    active
% 3.67/1.04  --res_prop_simpl_new                    false
% 3.67/1.04  --res_prop_simpl_given                  true
% 3.67/1.04  --res_passive_queue_type                priority_queues
% 3.67/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.04  --res_passive_queues_freq               [15;5]
% 3.67/1.04  --res_forward_subs                      full
% 3.67/1.04  --res_backward_subs                     full
% 3.67/1.04  --res_forward_subs_resolution           true
% 3.67/1.04  --res_backward_subs_resolution          true
% 3.67/1.04  --res_orphan_elimination                true
% 3.67/1.04  --res_time_limit                        2.
% 3.67/1.04  --res_out_proof                         true
% 3.67/1.04  
% 3.67/1.04  ------ Superposition Options
% 3.67/1.04  
% 3.67/1.04  --superposition_flag                    true
% 3.67/1.04  --sup_passive_queue_type                priority_queues
% 3.67/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.67/1.04  --demod_completeness_check              fast
% 3.67/1.04  --demod_use_ground                      true
% 3.67/1.04  --sup_to_prop_solver                    passive
% 3.67/1.04  --sup_prop_simpl_new                    true
% 3.67/1.04  --sup_prop_simpl_given                  true
% 3.67/1.04  --sup_fun_splitting                     true
% 3.67/1.04  --sup_smt_interval                      50000
% 3.67/1.04  
% 3.67/1.04  ------ Superposition Simplification Setup
% 3.67/1.04  
% 3.67/1.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/1.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/1.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/1.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/1.04  --sup_immed_triv                        [TrivRules]
% 3.67/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.04  --sup_immed_bw_main                     []
% 3.67/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.04  --sup_input_bw                          []
% 3.67/1.04  
% 3.67/1.04  ------ Combination Options
% 3.67/1.04  
% 3.67/1.04  --comb_res_mult                         3
% 3.67/1.04  --comb_sup_mult                         2
% 3.67/1.04  --comb_inst_mult                        10
% 3.67/1.04  
% 3.67/1.04  ------ Debug Options
% 3.67/1.04  
% 3.67/1.04  --dbg_backtrace                         false
% 3.67/1.04  --dbg_dump_prop_clauses                 false
% 3.67/1.04  --dbg_dump_prop_clauses_file            -
% 3.67/1.04  --dbg_out_stat                          false
% 3.67/1.04  
% 3.67/1.04  
% 3.67/1.04  
% 3.67/1.04  
% 3.67/1.04  ------ Proving...
% 3.67/1.04  
% 3.67/1.04  
% 3.67/1.04  % SZS status Theorem for theBenchmark.p
% 3.67/1.04  
% 3.67/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/1.04  
% 3.67/1.04  fof(f20,conjecture,(
% 3.67/1.04    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f21,negated_conjecture,(
% 3.67/1.04    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.67/1.04    inference(negated_conjecture,[],[f20])).
% 3.67/1.04  
% 3.67/1.04  fof(f47,plain,(
% 3.67/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.67/1.04    inference(ennf_transformation,[],[f21])).
% 3.67/1.04  
% 3.67/1.04  fof(f48,plain,(
% 3.67/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.67/1.04    inference(flattening,[],[f47])).
% 3.67/1.04  
% 3.67/1.04  fof(f64,plain,(
% 3.67/1.04    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 3.67/1.04    introduced(choice_axiom,[])).
% 3.67/1.04  
% 3.67/1.04  fof(f63,plain,(
% 3.67/1.04    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 3.67/1.04    introduced(choice_axiom,[])).
% 3.67/1.04  
% 3.67/1.04  fof(f62,plain,(
% 3.67/1.04    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 3.67/1.04    introduced(choice_axiom,[])).
% 3.67/1.04  
% 3.67/1.04  fof(f61,plain,(
% 3.67/1.04    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 3.67/1.04    introduced(choice_axiom,[])).
% 3.67/1.04  
% 3.67/1.04  fof(f60,plain,(
% 3.67/1.04    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 3.67/1.04    introduced(choice_axiom,[])).
% 3.67/1.04  
% 3.67/1.04  fof(f59,plain,(
% 3.67/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 3.67/1.04    introduced(choice_axiom,[])).
% 3.67/1.04  
% 3.67/1.04  fof(f65,plain,(
% 3.67/1.04    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 3.67/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f48,f64,f63,f62,f61,f60,f59])).
% 3.67/1.04  
% 3.67/1.04  fof(f110,plain,(
% 3.67/1.04    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f14,axiom,(
% 3.67/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f23,plain,(
% 3.67/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.67/1.04    inference(pure_predicate_removal,[],[f14])).
% 3.67/1.04  
% 3.67/1.04  fof(f36,plain,(
% 3.67/1.04    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.04    inference(ennf_transformation,[],[f23])).
% 3.67/1.04  
% 3.67/1.04  fof(f86,plain,(
% 3.67/1.04    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.04    inference(cnf_transformation,[],[f36])).
% 3.67/1.04  
% 3.67/1.04  fof(f11,axiom,(
% 3.67/1.04    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f31,plain,(
% 3.67/1.04    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.67/1.04    inference(ennf_transformation,[],[f11])).
% 3.67/1.04  
% 3.67/1.04  fof(f32,plain,(
% 3.67/1.04    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.67/1.04    inference(flattening,[],[f31])).
% 3.67/1.04  
% 3.67/1.04  fof(f82,plain,(
% 3.67/1.04    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f32])).
% 3.67/1.04  
% 3.67/1.04  fof(f13,axiom,(
% 3.67/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f35,plain,(
% 3.67/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.04    inference(ennf_transformation,[],[f13])).
% 3.67/1.04  
% 3.67/1.04  fof(f85,plain,(
% 3.67/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.04    inference(cnf_transformation,[],[f35])).
% 3.67/1.04  
% 3.67/1.04  fof(f2,axiom,(
% 3.67/1.04    v1_xboole_0(k1_xboole_0)),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f68,plain,(
% 3.67/1.04    v1_xboole_0(k1_xboole_0)),
% 3.67/1.04    inference(cnf_transformation,[],[f2])).
% 3.67/1.04  
% 3.67/1.04  fof(f4,axiom,(
% 3.67/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f52,plain,(
% 3.67/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/1.04    inference(nnf_transformation,[],[f4])).
% 3.67/1.04  
% 3.67/1.04  fof(f53,plain,(
% 3.67/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/1.04    inference(flattening,[],[f52])).
% 3.67/1.04  
% 3.67/1.04  fof(f73,plain,(
% 3.67/1.04    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.67/1.04    inference(cnf_transformation,[],[f53])).
% 3.67/1.04  
% 3.67/1.04  fof(f112,plain,(
% 3.67/1.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.67/1.04    inference(equality_resolution,[],[f73])).
% 3.67/1.04  
% 3.67/1.04  fof(f3,axiom,(
% 3.67/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f22,plain,(
% 3.67/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.67/1.04    inference(rectify,[],[f3])).
% 3.67/1.04  
% 3.67/1.04  fof(f24,plain,(
% 3.67/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.67/1.04    inference(ennf_transformation,[],[f22])).
% 3.67/1.04  
% 3.67/1.04  fof(f50,plain,(
% 3.67/1.04    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.67/1.04    introduced(choice_axiom,[])).
% 3.67/1.04  
% 3.67/1.04  fof(f51,plain,(
% 3.67/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.67/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f50])).
% 3.67/1.04  
% 3.67/1.04  fof(f70,plain,(
% 3.67/1.04    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f51])).
% 3.67/1.04  
% 3.67/1.04  fof(f8,axiom,(
% 3.67/1.04    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f27,plain,(
% 3.67/1.04    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.67/1.04    inference(ennf_transformation,[],[f8])).
% 3.67/1.04  
% 3.67/1.04  fof(f79,plain,(
% 3.67/1.04    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f27])).
% 3.67/1.04  
% 3.67/1.04  fof(f7,axiom,(
% 3.67/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f54,plain,(
% 3.67/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.67/1.04    inference(nnf_transformation,[],[f7])).
% 3.67/1.04  
% 3.67/1.04  fof(f78,plain,(
% 3.67/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f54])).
% 3.67/1.04  
% 3.67/1.04  fof(f1,axiom,(
% 3.67/1.04    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f49,plain,(
% 3.67/1.04    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.67/1.04    inference(nnf_transformation,[],[f1])).
% 3.67/1.04  
% 3.67/1.04  fof(f66,plain,(
% 3.67/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f49])).
% 3.67/1.04  
% 3.67/1.04  fof(f67,plain,(
% 3.67/1.04    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.67/1.04    inference(cnf_transformation,[],[f49])).
% 3.67/1.04  
% 3.67/1.04  fof(f10,axiom,(
% 3.67/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f29,plain,(
% 3.67/1.04    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.67/1.04    inference(ennf_transformation,[],[f10])).
% 3.67/1.04  
% 3.67/1.04  fof(f30,plain,(
% 3.67/1.04    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 3.67/1.04    inference(flattening,[],[f29])).
% 3.67/1.04  
% 3.67/1.04  fof(f81,plain,(
% 3.67/1.04    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f30])).
% 3.67/1.04  
% 3.67/1.04  fof(f103,plain,(
% 3.67/1.04    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f77,plain,(
% 3.67/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.67/1.04    inference(cnf_transformation,[],[f54])).
% 3.67/1.04  
% 3.67/1.04  fof(f5,axiom,(
% 3.67/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f25,plain,(
% 3.67/1.04    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.67/1.04    inference(ennf_transformation,[],[f5])).
% 3.67/1.04  
% 3.67/1.04  fof(f75,plain,(
% 3.67/1.04    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.67/1.04    inference(cnf_transformation,[],[f25])).
% 3.67/1.04  
% 3.67/1.04  fof(f107,plain,(
% 3.67/1.04    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f17,axiom,(
% 3.67/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f41,plain,(
% 3.67/1.04    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.67/1.04    inference(ennf_transformation,[],[f17])).
% 3.67/1.04  
% 3.67/1.04  fof(f42,plain,(
% 3.67/1.04    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.67/1.04    inference(flattening,[],[f41])).
% 3.67/1.04  
% 3.67/1.04  fof(f91,plain,(
% 3.67/1.04    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f42])).
% 3.67/1.04  
% 3.67/1.04  fof(f105,plain,(
% 3.67/1.04    v1_funct_1(sK5)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f108,plain,(
% 3.67/1.04    v1_funct_1(sK6)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f111,plain,(
% 3.67/1.04    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f12,axiom,(
% 3.67/1.04    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f33,plain,(
% 3.67/1.04    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.67/1.04    inference(ennf_transformation,[],[f12])).
% 3.67/1.04  
% 3.67/1.04  fof(f34,plain,(
% 3.67/1.04    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.67/1.04    inference(flattening,[],[f33])).
% 3.67/1.04  
% 3.67/1.04  fof(f55,plain,(
% 3.67/1.04    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.67/1.04    inference(nnf_transformation,[],[f34])).
% 3.67/1.04  
% 3.67/1.04  fof(f83,plain,(
% 3.67/1.04    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f55])).
% 3.67/1.04  
% 3.67/1.04  fof(f104,plain,(
% 3.67/1.04    r1_subset_1(sK3,sK4)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f100,plain,(
% 3.67/1.04    ~v1_xboole_0(sK3)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f102,plain,(
% 3.67/1.04    ~v1_xboole_0(sK4)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f9,axiom,(
% 3.67/1.04    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f28,plain,(
% 3.67/1.04    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.67/1.04    inference(ennf_transformation,[],[f9])).
% 3.67/1.04  
% 3.67/1.04  fof(f80,plain,(
% 3.67/1.04    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f28])).
% 3.67/1.04  
% 3.67/1.04  fof(f15,axiom,(
% 3.67/1.04    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f37,plain,(
% 3.67/1.04    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.67/1.04    inference(ennf_transformation,[],[f15])).
% 3.67/1.04  
% 3.67/1.04  fof(f38,plain,(
% 3.67/1.04    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.67/1.04    inference(flattening,[],[f37])).
% 3.67/1.04  
% 3.67/1.04  fof(f88,plain,(
% 3.67/1.04    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f38])).
% 3.67/1.04  
% 3.67/1.04  fof(f16,axiom,(
% 3.67/1.04    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f39,plain,(
% 3.67/1.04    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.67/1.04    inference(ennf_transformation,[],[f16])).
% 3.67/1.04  
% 3.67/1.04  fof(f40,plain,(
% 3.67/1.04    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.67/1.04    inference(flattening,[],[f39])).
% 3.67/1.04  
% 3.67/1.04  fof(f56,plain,(
% 3.67/1.04    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.67/1.04    inference(nnf_transformation,[],[f40])).
% 3.67/1.04  
% 3.67/1.04  fof(f89,plain,(
% 3.67/1.04    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f56])).
% 3.67/1.04  
% 3.67/1.04  fof(f99,plain,(
% 3.67/1.04    ~v1_xboole_0(sK2)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f106,plain,(
% 3.67/1.04    v1_funct_2(sK5,sK3,sK2)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f98,plain,(
% 3.67/1.04    ~v1_xboole_0(sK1)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f101,plain,(
% 3.67/1.04    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f18,axiom,(
% 3.67/1.04    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f43,plain,(
% 3.67/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.67/1.04    inference(ennf_transformation,[],[f18])).
% 3.67/1.04  
% 3.67/1.04  fof(f44,plain,(
% 3.67/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.67/1.04    inference(flattening,[],[f43])).
% 3.67/1.04  
% 3.67/1.04  fof(f57,plain,(
% 3.67/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.67/1.04    inference(nnf_transformation,[],[f44])).
% 3.67/1.04  
% 3.67/1.04  fof(f58,plain,(
% 3.67/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.67/1.04    inference(flattening,[],[f57])).
% 3.67/1.04  
% 3.67/1.04  fof(f93,plain,(
% 3.67/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f58])).
% 3.67/1.04  
% 3.67/1.04  fof(f117,plain,(
% 3.67/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/1.04    inference(equality_resolution,[],[f93])).
% 3.67/1.04  
% 3.67/1.04  fof(f19,axiom,(
% 3.67/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.67/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.04  
% 3.67/1.04  fof(f45,plain,(
% 3.67/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.67/1.04    inference(ennf_transformation,[],[f19])).
% 3.67/1.04  
% 3.67/1.04  fof(f46,plain,(
% 3.67/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.67/1.04    inference(flattening,[],[f45])).
% 3.67/1.04  
% 3.67/1.04  fof(f95,plain,(
% 3.67/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f46])).
% 3.67/1.04  
% 3.67/1.04  fof(f96,plain,(
% 3.67/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f46])).
% 3.67/1.04  
% 3.67/1.04  fof(f97,plain,(
% 3.67/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f46])).
% 3.67/1.04  
% 3.67/1.04  fof(f109,plain,(
% 3.67/1.04    v1_funct_2(sK6,sK4,sK2)),
% 3.67/1.04    inference(cnf_transformation,[],[f65])).
% 3.67/1.04  
% 3.67/1.04  fof(f92,plain,(
% 3.67/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/1.04    inference(cnf_transformation,[],[f58])).
% 3.67/1.04  
% 3.67/1.04  fof(f118,plain,(
% 3.67/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/1.04    inference(equality_resolution,[],[f92])).
% 3.67/1.04  
% 3.67/1.04  cnf(c_33,negated_conjecture,
% 3.67/1.04      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.67/1.04      inference(cnf_transformation,[],[f110]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2292,plain,
% 3.67/1.04      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_20,plain,
% 3.67/1.04      ( v4_relat_1(X0,X1)
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.67/1.04      inference(cnf_transformation,[],[f86]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_16,plain,
% 3.67/1.04      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.67/1.04      inference(cnf_transformation,[],[f82]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_621,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ v1_relat_1(X0)
% 3.67/1.04      | k7_relat_1(X0,X1) = X0 ),
% 3.67/1.04      inference(resolution,[status(thm)],[c_20,c_16]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_19,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | v1_relat_1(X0) ),
% 3.67/1.04      inference(cnf_transformation,[],[f85]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_625,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | k7_relat_1(X0,X1) = X0 ),
% 3.67/1.04      inference(global_propositional_subsumption,
% 3.67/1.04                [status(thm)],
% 3.67/1.04                [c_621,c_20,c_19,c_16]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2274,plain,
% 3.67/1.04      ( k7_relat_1(X0,X1) = X0
% 3.67/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_3489,plain,
% 3.67/1.04      ( k7_relat_1(sK6,sK4) = sK6 ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2292,c_2274]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2298,plain,
% 3.67/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/1.04      | v1_relat_1(X0) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4003,plain,
% 3.67/1.04      ( v1_relat_1(sK6) = iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2292,c_2298]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2,plain,
% 3.67/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 3.67/1.04      inference(cnf_transformation,[],[f68]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2308,plain,
% 3.67/1.04      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_7,plain,
% 3.67/1.04      ( r1_tarski(X0,X0) ),
% 3.67/1.04      inference(cnf_transformation,[],[f112]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2303,plain,
% 3.67/1.04      ( r1_tarski(X0,X0) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4,plain,
% 3.67/1.04      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.67/1.04      inference(cnf_transformation,[],[f70]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2306,plain,
% 3.67/1.04      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.67/1.04      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_13,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.67/1.04      | ~ r2_hidden(X2,X0)
% 3.67/1.04      | ~ v1_xboole_0(X1) ),
% 3.67/1.04      inference(cnf_transformation,[],[f79]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_11,plain,
% 3.67/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.67/1.04      inference(cnf_transformation,[],[f78]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_344,plain,
% 3.67/1.04      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.67/1.04      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_345,plain,
% 3.67/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.67/1.04      inference(renaming,[status(thm)],[c_344]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_436,plain,
% 3.67/1.04      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 3.67/1.04      inference(bin_hyper_res,[status(thm)],[c_13,c_345]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2276,plain,
% 3.67/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.67/1.04      | r2_hidden(X2,X0) != iProver_top
% 3.67/1.04      | v1_xboole_0(X1) != iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4067,plain,
% 3.67/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.67/1.04      | r1_xboole_0(X2,X0) = iProver_top
% 3.67/1.04      | v1_xboole_0(X1) != iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2306,c_2276]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_8111,plain,
% 3.67/1.04      ( r1_xboole_0(X0,X1) = iProver_top
% 3.67/1.04      | v1_xboole_0(X1) != iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2303,c_4067]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_1,plain,
% 3.67/1.04      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.67/1.04      inference(cnf_transformation,[],[f66]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2309,plain,
% 3.67/1.04      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.67/1.04      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_8214,plain,
% 3.67/1.04      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.67/1.04      | v1_xboole_0(X1) != iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_8111,c_2309]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_8219,plain,
% 3.67/1.04      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2308,c_8214]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_0,plain,
% 3.67/1.04      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.67/1.04      inference(cnf_transformation,[],[f67]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2310,plain,
% 3.67/1.04      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 3.67/1.04      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_8640,plain,
% 3.67/1.04      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_8219,c_2310]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_15,plain,
% 3.67/1.04      ( ~ r1_xboole_0(X0,X1)
% 3.67/1.04      | ~ v1_relat_1(X2)
% 3.67/1.04      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 3.67/1.04      inference(cnf_transformation,[],[f81]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2299,plain,
% 3.67/1.04      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 3.67/1.04      | r1_xboole_0(X1,X2) != iProver_top
% 3.67/1.04      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_8671,plain,
% 3.67/1.04      ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
% 3.67/1.04      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_8640,c_2299]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_8713,plain,
% 3.67/1.04      ( k7_relat_1(k7_relat_1(sK6,X0),k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_4003,c_8671]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_8757,plain,
% 3.67/1.04      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_3489,c_8713]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_40,negated_conjecture,
% 3.67/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 3.67/1.04      inference(cnf_transformation,[],[f103]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2286,plain,
% 3.67/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_12,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.67/1.04      inference(cnf_transformation,[],[f77]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2301,plain,
% 3.67/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.67/1.04      | r1_tarski(X0,X1) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_3592,plain,
% 3.67/1.04      ( r1_tarski(sK4,sK1) = iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2286,c_2301]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_9,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.67/1.04      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.67/1.04      inference(cnf_transformation,[],[f75]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_432,plain,
% 3.67/1.04      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.67/1.04      inference(bin_hyper_res,[status(thm)],[c_9,c_345]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2278,plain,
% 3.67/1.04      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.67/1.04      | r1_tarski(X2,X0) != iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_7319,plain,
% 3.67/1.04      ( k9_subset_1(sK1,X0,sK4) = k3_xboole_0(X0,sK4) ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_3592,c_2278]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_36,negated_conjecture,
% 3.67/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 3.67/1.04      inference(cnf_transformation,[],[f107]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2289,plain,
% 3.67/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_25,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ v1_funct_1(X0)
% 3.67/1.04      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.67/1.04      inference(cnf_transformation,[],[f91]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2297,plain,
% 3.67/1.04      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.67/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/1.04      | v1_funct_1(X2) != iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4343,plain,
% 3.67/1.04      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 3.67/1.04      | v1_funct_1(sK5) != iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2289,c_2297]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_38,negated_conjecture,
% 3.67/1.04      ( v1_funct_1(sK5) ),
% 3.67/1.04      inference(cnf_transformation,[],[f105]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_53,plain,
% 3.67/1.04      ( v1_funct_1(sK5) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4918,plain,
% 3.67/1.04      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.67/1.04      inference(global_propositional_subsumption,
% 3.67/1.04                [status(thm)],
% 3.67/1.04                [c_4343,c_53]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4342,plain,
% 3.67/1.04      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 3.67/1.04      | v1_funct_1(sK6) != iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2292,c_2297]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_35,negated_conjecture,
% 3.67/1.04      ( v1_funct_1(sK6) ),
% 3.67/1.04      inference(cnf_transformation,[],[f108]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_56,plain,
% 3.67/1.04      ( v1_funct_1(sK6) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4846,plain,
% 3.67/1.04      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.67/1.04      inference(global_propositional_subsumption,
% 3.67/1.04                [status(thm)],
% 3.67/1.04                [c_4342,c_56]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_32,negated_conjecture,
% 3.67/1.04      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.67/1.04      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.67/1.04      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 3.67/1.04      inference(cnf_transformation,[],[f111]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4849,plain,
% 3.67/1.04      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.67/1.04      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.67/1.04      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 3.67/1.04      inference(demodulation,[status(thm)],[c_4846,c_32]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4921,plain,
% 3.67/1.04      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.67/1.04      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.67/1.04      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 3.67/1.04      inference(demodulation,[status(thm)],[c_4918,c_4849]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_7425,plain,
% 3.67/1.04      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.67/1.04      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.67/1.04      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4)) ),
% 3.67/1.04      inference(demodulation,[status(thm)],[c_7319,c_4921]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_18,plain,
% 3.67/1.04      ( ~ r1_subset_1(X0,X1)
% 3.67/1.04      | r1_xboole_0(X0,X1)
% 3.67/1.04      | v1_xboole_0(X0)
% 3.67/1.04      | v1_xboole_0(X1) ),
% 3.67/1.04      inference(cnf_transformation,[],[f83]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_39,negated_conjecture,
% 3.67/1.04      ( r1_subset_1(sK3,sK4) ),
% 3.67/1.04      inference(cnf_transformation,[],[f104]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_588,plain,
% 3.67/1.04      ( r1_xboole_0(X0,X1)
% 3.67/1.04      | v1_xboole_0(X0)
% 3.67/1.04      | v1_xboole_0(X1)
% 3.67/1.04      | sK4 != X1
% 3.67/1.04      | sK3 != X0 ),
% 3.67/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_589,plain,
% 3.67/1.04      ( r1_xboole_0(sK3,sK4) | v1_xboole_0(sK4) | v1_xboole_0(sK3) ),
% 3.67/1.04      inference(unflattening,[status(thm)],[c_588]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_43,negated_conjecture,
% 3.67/1.04      ( ~ v1_xboole_0(sK3) ),
% 3.67/1.04      inference(cnf_transformation,[],[f100]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_41,negated_conjecture,
% 3.67/1.04      ( ~ v1_xboole_0(sK4) ),
% 3.67/1.04      inference(cnf_transformation,[],[f102]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_591,plain,
% 3.67/1.04      ( r1_xboole_0(sK3,sK4) ),
% 3.67/1.04      inference(global_propositional_subsumption,
% 3.67/1.04                [status(thm)],
% 3.67/1.04                [c_589,c_43,c_41]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2275,plain,
% 3.67/1.04      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_3405,plain,
% 3.67/1.04      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2275,c_2309]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4004,plain,
% 3.67/1.04      ( v1_relat_1(sK5) = iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2289,c_2298]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4167,plain,
% 3.67/1.04      ( k7_relat_1(k7_relat_1(X0,sK3),sK4) = k1_xboole_0
% 3.67/1.04      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2275,c_2299]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4266,plain,
% 3.67/1.04      ( k7_relat_1(k7_relat_1(sK5,sK3),sK4) = k1_xboole_0 ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_4004,c_4167]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_3490,plain,
% 3.67/1.04      ( k7_relat_1(sK5,sK3) = sK5 ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2289,c_2274]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_14,plain,
% 3.67/1.04      ( ~ v1_relat_1(X0)
% 3.67/1.04      | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
% 3.67/1.04      inference(cnf_transformation,[],[f80]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2300,plain,
% 3.67/1.04      ( k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1)
% 3.67/1.04      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4170,plain,
% 3.67/1.04      ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0)) = k7_relat_1(sK5,X0) ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_4004,c_2300]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_21,plain,
% 3.67/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.04      | v1_partfun1(X0,X1)
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ v1_funct_1(X0)
% 3.67/1.04      | v1_xboole_0(X2) ),
% 3.67/1.04      inference(cnf_transformation,[],[f88]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_24,plain,
% 3.67/1.04      ( ~ v1_partfun1(X0,X1)
% 3.67/1.04      | ~ v4_relat_1(X0,X1)
% 3.67/1.04      | ~ v1_relat_1(X0)
% 3.67/1.04      | k1_relat_1(X0) = X1 ),
% 3.67/1.04      inference(cnf_transformation,[],[f89]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_601,plain,
% 3.67/1.04      ( ~ v1_partfun1(X0,X1)
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ v1_relat_1(X0)
% 3.67/1.04      | k1_relat_1(X0) = X1 ),
% 3.67/1.04      inference(resolution,[status(thm)],[c_20,c_24]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_605,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ v1_partfun1(X0,X1)
% 3.67/1.04      | k1_relat_1(X0) = X1 ),
% 3.67/1.04      inference(global_propositional_subsumption,
% 3.67/1.04                [status(thm)],
% 3.67/1.04                [c_601,c_24,c_20,c_19]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_606,plain,
% 3.67/1.04      ( ~ v1_partfun1(X0,X1)
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | k1_relat_1(X0) = X1 ),
% 3.67/1.04      inference(renaming,[status(thm)],[c_605]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_696,plain,
% 3.67/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.67/1.04      | ~ v1_funct_1(X0)
% 3.67/1.04      | v1_xboole_0(X2)
% 3.67/1.04      | k1_relat_1(X0) = X1 ),
% 3.67/1.04      inference(resolution,[status(thm)],[c_21,c_606]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_700,plain,
% 3.67/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ v1_funct_2(X0,X1,X2)
% 3.67/1.04      | ~ v1_funct_1(X0)
% 3.67/1.04      | v1_xboole_0(X2)
% 3.67/1.04      | k1_relat_1(X0) = X1 ),
% 3.67/1.04      inference(global_propositional_subsumption,
% 3.67/1.04                [status(thm)],
% 3.67/1.04                [c_696,c_24,c_21,c_20,c_19]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_701,plain,
% 3.67/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ v1_funct_1(X0)
% 3.67/1.04      | v1_xboole_0(X2)
% 3.67/1.04      | k1_relat_1(X0) = X1 ),
% 3.67/1.04      inference(renaming,[status(thm)],[c_700]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2273,plain,
% 3.67/1.04      ( k1_relat_1(X0) = X1
% 3.67/1.04      | v1_funct_2(X0,X1,X2) != iProver_top
% 3.67/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/1.04      | v1_funct_1(X0) != iProver_top
% 3.67/1.04      | v1_xboole_0(X2) = iProver_top ),
% 3.67/1.04      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_3208,plain,
% 3.67/1.04      ( k1_relat_1(sK5) = sK3
% 3.67/1.04      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.67/1.04      | v1_funct_1(sK5) != iProver_top
% 3.67/1.04      | v1_xboole_0(sK2) = iProver_top ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_2289,c_2273]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_44,negated_conjecture,
% 3.67/1.04      ( ~ v1_xboole_0(sK2) ),
% 3.67/1.04      inference(cnf_transformation,[],[f99]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_37,negated_conjecture,
% 3.67/1.04      ( v1_funct_2(sK5,sK3,sK2) ),
% 3.67/1.04      inference(cnf_transformation,[],[f106]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2476,plain,
% 3.67/1.04      ( ~ v1_funct_2(X0,X1,sK2)
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 3.67/1.04      | ~ v1_funct_1(X0)
% 3.67/1.04      | v1_xboole_0(sK2)
% 3.67/1.04      | k1_relat_1(X0) = X1 ),
% 3.67/1.04      inference(instantiation,[status(thm)],[c_701]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2685,plain,
% 3.67/1.04      ( ~ v1_funct_2(sK5,X0,sK2)
% 3.67/1.04      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 3.67/1.04      | ~ v1_funct_1(sK5)
% 3.67/1.04      | v1_xboole_0(sK2)
% 3.67/1.04      | k1_relat_1(sK5) = X0 ),
% 3.67/1.04      inference(instantiation,[status(thm)],[c_2476]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_2687,plain,
% 3.67/1.04      ( ~ v1_funct_2(sK5,sK3,sK2)
% 3.67/1.04      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.67/1.04      | ~ v1_funct_1(sK5)
% 3.67/1.04      | v1_xboole_0(sK2)
% 3.67/1.04      | k1_relat_1(sK5) = sK3 ),
% 3.67/1.04      inference(instantiation,[status(thm)],[c_2685]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_3311,plain,
% 3.67/1.04      ( k1_relat_1(sK5) = sK3 ),
% 3.67/1.04      inference(global_propositional_subsumption,
% 3.67/1.04                [status(thm)],
% 3.67/1.04                [c_3208,c_44,c_38,c_37,c_36,c_2687]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4171,plain,
% 3.67/1.04      ( k7_relat_1(sK5,k3_xboole_0(sK3,X0)) = k7_relat_1(sK5,X0) ),
% 3.67/1.04      inference(light_normalisation,[status(thm)],[c_4170,c_3311]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4210,plain,
% 3.67/1.04      ( k7_relat_1(sK5,sK4) = k7_relat_1(sK5,k1_xboole_0) ),
% 3.67/1.04      inference(superposition,[status(thm)],[c_3405,c_4171]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_4267,plain,
% 3.67/1.04      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.04      inference(light_normalisation,[status(thm)],[c_4266,c_3490,c_4210]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_7426,plain,
% 3.67/1.04      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.67/1.04      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.67/1.04      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.67/1.04      inference(light_normalisation,[status(thm)],[c_7425,c_3405,c_4267]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_45,negated_conjecture,
% 3.67/1.04      ( ~ v1_xboole_0(sK1) ),
% 3.67/1.04      inference(cnf_transformation,[],[f98]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_42,negated_conjecture,
% 3.67/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.67/1.04      inference(cnf_transformation,[],[f101]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_27,plain,
% 3.67/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.04      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.04      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.67/1.04      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.04      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.67/1.04      | ~ v1_funct_1(X0)
% 3.67/1.04      | ~ v1_funct_1(X3)
% 3.67/1.04      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.67/1.04      | v1_xboole_0(X5)
% 3.67/1.04      | v1_xboole_0(X2)
% 3.67/1.04      | v1_xboole_0(X4)
% 3.67/1.04      | v1_xboole_0(X1)
% 3.67/1.04      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.67/1.04      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.67/1.04      inference(cnf_transformation,[],[f117]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_31,plain,
% 3.67/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.04      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.04      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.04      | ~ v1_funct_1(X0)
% 3.67/1.04      | ~ v1_funct_1(X3)
% 3.67/1.04      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.67/1.04      | v1_xboole_0(X5)
% 3.67/1.04      | v1_xboole_0(X2)
% 3.67/1.04      | v1_xboole_0(X4)
% 3.67/1.04      | v1_xboole_0(X1) ),
% 3.67/1.04      inference(cnf_transformation,[],[f95]) ).
% 3.67/1.04  
% 3.67/1.04  cnf(c_30,plain,
% 3.67/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.04      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.04      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.67/1.04      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.05      | ~ v1_funct_1(X0)
% 3.67/1.05      | ~ v1_funct_1(X3)
% 3.67/1.05      | v1_xboole_0(X5)
% 3.67/1.05      | v1_xboole_0(X2)
% 3.67/1.05      | v1_xboole_0(X4)
% 3.67/1.05      | v1_xboole_0(X1) ),
% 3.67/1.05      inference(cnf_transformation,[],[f96]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_29,plain,
% 3.67/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.05      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.05      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.67/1.05      | ~ v1_funct_1(X0)
% 3.67/1.05      | ~ v1_funct_1(X3)
% 3.67/1.05      | v1_xboole_0(X5)
% 3.67/1.05      | v1_xboole_0(X2)
% 3.67/1.05      | v1_xboole_0(X4)
% 3.67/1.05      | v1_xboole_0(X1) ),
% 3.67/1.05      inference(cnf_transformation,[],[f97]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_255,plain,
% 3.67/1.05      ( ~ v1_funct_1(X3)
% 3.67/1.05      | ~ v1_funct_1(X0)
% 3.67/1.05      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.05      | ~ v1_funct_2(X0,X1,X2)
% 3.67/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.05      | v1_xboole_0(X5)
% 3.67/1.05      | v1_xboole_0(X2)
% 3.67/1.05      | v1_xboole_0(X4)
% 3.67/1.05      | v1_xboole_0(X1)
% 3.67/1.05      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.67/1.05      inference(global_propositional_subsumption,
% 3.67/1.05                [status(thm)],
% 3.67/1.05                [c_27,c_31,c_30,c_29]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_256,plain,
% 3.67/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.05      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.05      | ~ v1_funct_1(X0)
% 3.67/1.05      | ~ v1_funct_1(X3)
% 3.67/1.05      | v1_xboole_0(X1)
% 3.67/1.05      | v1_xboole_0(X2)
% 3.67/1.05      | v1_xboole_0(X4)
% 3.67/1.05      | v1_xboole_0(X5)
% 3.67/1.05      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.67/1.05      inference(renaming,[status(thm)],[c_255]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_2279,plain,
% 3.67/1.05      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.67/1.05      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.67/1.05      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.67/1.05      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.67/1.05      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.67/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/1.05      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.67/1.05      | v1_funct_1(X2) != iProver_top
% 3.67/1.05      | v1_funct_1(X5) != iProver_top
% 3.67/1.05      | v1_xboole_0(X3) = iProver_top
% 3.67/1.05      | v1_xboole_0(X1) = iProver_top
% 3.67/1.05      | v1_xboole_0(X4) = iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_6774,plain,
% 3.67/1.05      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 3.67/1.05      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.67/1.05      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 3.67/1.05      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.67/1.05      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | v1_funct_1(X1) != iProver_top
% 3.67/1.05      | v1_funct_1(sK6) != iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top
% 3.67/1.05      | v1_xboole_0(X2) = iProver_top
% 3.67/1.05      | v1_xboole_0(sK2) = iProver_top
% 3.67/1.05      | v1_xboole_0(sK4) = iProver_top ),
% 3.67/1.05      inference(superposition,[status(thm)],[c_4846,c_2279]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_47,plain,
% 3.67/1.05      ( v1_xboole_0(sK2) != iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_50,plain,
% 3.67/1.05      ( v1_xboole_0(sK4) != iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_34,negated_conjecture,
% 3.67/1.05      ( v1_funct_2(sK6,sK4,sK2) ),
% 3.67/1.05      inference(cnf_transformation,[],[f109]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_57,plain,
% 3.67/1.05      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_58,plain,
% 3.67/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_6898,plain,
% 3.67/1.05      ( v1_funct_1(X1) != iProver_top
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.67/1.05      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 3.67/1.05      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.67/1.05      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top
% 3.67/1.05      | v1_xboole_0(X2) = iProver_top ),
% 3.67/1.05      inference(global_propositional_subsumption,
% 3.67/1.05                [status(thm)],
% 3.67/1.05                [c_6774,c_47,c_50,c_56,c_57,c_58]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_6899,plain,
% 3.67/1.05      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 3.67/1.05      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.67/1.05      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | v1_funct_1(X1) != iProver_top
% 3.67/1.05      | v1_xboole_0(X2) = iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top ),
% 3.67/1.05      inference(renaming,[status(thm)],[c_6898]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_6905,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.67/1.05      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.67/1.05      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.67/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | v1_funct_1(sK5) != iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top
% 3.67/1.05      | v1_xboole_0(sK3) = iProver_top ),
% 3.67/1.05      inference(superposition,[status(thm)],[c_4918,c_6899]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_48,plain,
% 3.67/1.05      ( v1_xboole_0(sK3) != iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_54,plain,
% 3.67/1.05      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_55,plain,
% 3.67/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7027,plain,
% 3.67/1.05      ( v1_xboole_0(X0) = iProver_top
% 3.67/1.05      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.67/1.05      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 3.67/1.05      inference(global_propositional_subsumption,
% 3.67/1.05                [status(thm)],
% 3.67/1.05                [c_6905,c_48,c_53,c_54,c_55]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7028,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.67/1.05      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top ),
% 3.67/1.05      inference(renaming,[status(thm)],[c_7027]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7434,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.67/1.05      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | v1_xboole_0(sK1) = iProver_top ),
% 3.67/1.05      inference(superposition,[status(thm)],[c_7319,c_7028]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7435,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.67/1.05      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | v1_xboole_0(sK1) = iProver_top ),
% 3.67/1.05      inference(light_normalisation,[status(thm)],[c_7434,c_3405]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7436,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.67/1.05      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,sK4)
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | v1_xboole_0(sK1) = iProver_top ),
% 3.67/1.05      inference(demodulation,[status(thm)],[c_7435,c_4171,c_7319]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7437,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.67/1.05      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | v1_xboole_0(sK1) = iProver_top ),
% 3.67/1.05      inference(light_normalisation,[status(thm)],[c_7436,c_4210,c_4267]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7445,plain,
% 3.67/1.05      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 3.67/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.67/1.05      | v1_xboole_0(sK1)
% 3.67/1.05      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.67/1.05      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.67/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_7437]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_28,plain,
% 3.67/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.05      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.05      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.67/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.05      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.67/1.05      | ~ v1_funct_1(X0)
% 3.67/1.05      | ~ v1_funct_1(X3)
% 3.67/1.05      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.67/1.05      | v1_xboole_0(X5)
% 3.67/1.05      | v1_xboole_0(X2)
% 3.67/1.05      | v1_xboole_0(X4)
% 3.67/1.05      | v1_xboole_0(X1)
% 3.67/1.05      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.67/1.05      inference(cnf_transformation,[],[f118]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_248,plain,
% 3.67/1.05      ( ~ v1_funct_1(X3)
% 3.67/1.05      | ~ v1_funct_1(X0)
% 3.67/1.05      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.05      | ~ v1_funct_2(X0,X1,X2)
% 3.67/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.05      | v1_xboole_0(X5)
% 3.67/1.05      | v1_xboole_0(X2)
% 3.67/1.05      | v1_xboole_0(X4)
% 3.67/1.05      | v1_xboole_0(X1)
% 3.67/1.05      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.67/1.05      inference(global_propositional_subsumption,
% 3.67/1.05                [status(thm)],
% 3.67/1.05                [c_28,c_31,c_30,c_29]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_249,plain,
% 3.67/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.05      | ~ v1_funct_2(X3,X4,X2)
% 3.67/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.67/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/1.05      | ~ v1_funct_1(X0)
% 3.67/1.05      | ~ v1_funct_1(X3)
% 3.67/1.05      | v1_xboole_0(X1)
% 3.67/1.05      | v1_xboole_0(X2)
% 3.67/1.05      | v1_xboole_0(X4)
% 3.67/1.05      | v1_xboole_0(X5)
% 3.67/1.05      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.67/1.05      inference(renaming,[status(thm)],[c_248]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_2280,plain,
% 3.67/1.05      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.67/1.05      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.67/1.05      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.67/1.05      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.67/1.05      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.67/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/1.05      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.67/1.05      | v1_funct_1(X2) != iProver_top
% 3.67/1.05      | v1_funct_1(X5) != iProver_top
% 3.67/1.05      | v1_xboole_0(X3) = iProver_top
% 3.67/1.05      | v1_xboole_0(X1) = iProver_top
% 3.67/1.05      | v1_xboole_0(X4) = iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top ),
% 3.67/1.05      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7147,plain,
% 3.67/1.05      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 3.67/1.05      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.67/1.05      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 3.67/1.05      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.67/1.05      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | v1_funct_1(X1) != iProver_top
% 3.67/1.05      | v1_funct_1(sK6) != iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top
% 3.67/1.05      | v1_xboole_0(X2) = iProver_top
% 3.67/1.05      | v1_xboole_0(sK2) = iProver_top
% 3.67/1.05      | v1_xboole_0(sK4) = iProver_top ),
% 3.67/1.05      inference(superposition,[status(thm)],[c_4846,c_2280]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7902,plain,
% 3.67/1.05      ( v1_funct_1(X1) != iProver_top
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.67/1.05      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 3.67/1.05      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.67/1.05      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top
% 3.67/1.05      | v1_xboole_0(X2) = iProver_top ),
% 3.67/1.05      inference(global_propositional_subsumption,
% 3.67/1.05                [status(thm)],
% 3.67/1.05                [c_7147,c_47,c_50,c_56,c_57,c_58]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7903,plain,
% 3.67/1.05      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.67/1.05      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 3.67/1.05      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.67/1.05      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.67/1.05      | v1_funct_1(X1) != iProver_top
% 3.67/1.05      | v1_xboole_0(X2) = iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top ),
% 3.67/1.05      inference(renaming,[status(thm)],[c_7902]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7909,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.67/1.05      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.67/1.05      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.67/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | v1_funct_1(sK5) != iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top
% 3.67/1.05      | v1_xboole_0(sK3) = iProver_top ),
% 3.67/1.05      inference(superposition,[status(thm)],[c_4918,c_7903]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7949,plain,
% 3.67/1.05      ( v1_xboole_0(X0) = iProver_top
% 3.67/1.05      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.67/1.05      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 3.67/1.05      inference(global_propositional_subsumption,
% 3.67/1.05                [status(thm)],
% 3.67/1.05                [c_7909,c_48,c_53,c_54,c_55]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7950,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.67/1.05      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.67/1.05      | v1_xboole_0(X0) = iProver_top ),
% 3.67/1.05      inference(renaming,[status(thm)],[c_7949]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7955,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.67/1.05      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | v1_xboole_0(sK1) = iProver_top ),
% 3.67/1.05      inference(superposition,[status(thm)],[c_7319,c_7950]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7960,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.67/1.05      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | v1_xboole_0(sK1) = iProver_top ),
% 3.67/1.05      inference(light_normalisation,[status(thm)],[c_7955,c_3405]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7961,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.67/1.05      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,sK4)
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | v1_xboole_0(sK1) = iProver_top ),
% 3.67/1.05      inference(demodulation,[status(thm)],[c_7960,c_4171,c_7319]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7962,plain,
% 3.67/1.05      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.67/1.05      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0
% 3.67/1.05      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.05      | v1_xboole_0(sK1) = iProver_top ),
% 3.67/1.05      inference(light_normalisation,[status(thm)],[c_7961,c_4210,c_4267]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_7964,plain,
% 3.67/1.05      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 3.67/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.67/1.05      | v1_xboole_0(sK1)
% 3.67/1.05      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.67/1.05      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.67/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_7962]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(c_8525,plain,
% 3.67/1.05      ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.67/1.05      inference(global_propositional_subsumption,
% 3.67/1.05                [status(thm)],
% 3.67/1.05                [c_7426,c_45,c_42,c_40,c_7445,c_7964]) ).
% 3.67/1.05  
% 3.67/1.05  cnf(contradiction,plain,
% 3.67/1.05      ( $false ),
% 3.67/1.05      inference(minisat,[status(thm)],[c_8757,c_8525]) ).
% 3.67/1.05  
% 3.67/1.05  
% 3.67/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/1.05  
% 3.67/1.05  ------                               Statistics
% 3.67/1.05  
% 3.67/1.05  ------ General
% 3.67/1.05  
% 3.67/1.05  abstr_ref_over_cycles:                  0
% 3.67/1.05  abstr_ref_under_cycles:                 0
% 3.67/1.05  gc_basic_clause_elim:                   0
% 3.67/1.05  forced_gc_time:                         0
% 3.67/1.05  parsing_time:                           0.015
% 3.67/1.05  unif_index_cands_time:                  0.
% 3.67/1.05  unif_index_add_time:                    0.
% 3.67/1.05  orderings_time:                         0.
% 3.67/1.05  out_proof_time:                         0.017
% 3.67/1.05  total_time:                             0.491
% 3.67/1.05  num_of_symbols:                         59
% 3.67/1.05  num_of_terms:                           19339
% 3.67/1.05  
% 3.67/1.05  ------ Preprocessing
% 3.67/1.05  
% 3.67/1.05  num_of_splits:                          0
% 3.67/1.05  num_of_split_atoms:                     0
% 3.67/1.05  num_of_reused_defs:                     0
% 3.67/1.05  num_eq_ax_congr_red:                    28
% 3.67/1.05  num_of_sem_filtered_clauses:            1
% 3.67/1.05  num_of_subtypes:                        0
% 3.67/1.05  monotx_restored_types:                  0
% 3.67/1.05  sat_num_of_epr_types:                   0
% 3.67/1.05  sat_num_of_non_cyclic_types:            0
% 3.67/1.05  sat_guarded_non_collapsed_types:        0
% 3.67/1.05  num_pure_diseq_elim:                    0
% 3.67/1.05  simp_replaced_by:                       0
% 3.67/1.05  res_preprocessed:                       194
% 3.67/1.05  prep_upred:                             0
% 3.67/1.05  prep_unflattend:                        32
% 3.67/1.05  smt_new_axioms:                         0
% 3.67/1.05  pred_elim_cands:                        8
% 3.67/1.05  pred_elim:                              3
% 3.67/1.05  pred_elim_cl:                           5
% 3.67/1.05  pred_elim_cycles:                       7
% 3.67/1.05  merged_defs:                            16
% 3.67/1.05  merged_defs_ncl:                        0
% 3.67/1.05  bin_hyper_res:                          19
% 3.67/1.05  prep_cycles:                            4
% 3.67/1.05  pred_elim_time:                         0.015
% 3.67/1.05  splitting_time:                         0.
% 3.67/1.05  sem_filter_time:                        0.
% 3.67/1.05  monotx_time:                            0.001
% 3.67/1.05  subtype_inf_time:                       0.
% 3.67/1.05  
% 3.67/1.05  ------ Problem properties
% 3.67/1.05  
% 3.67/1.05  clauses:                                39
% 3.67/1.05  conjectures:                            13
% 3.67/1.05  epr:                                    15
% 3.67/1.05  horn:                                   30
% 3.67/1.05  ground:                                 15
% 3.67/1.05  unary:                                  15
% 3.67/1.05  binary:                                 10
% 3.67/1.05  lits:                                   145
% 3.67/1.05  lits_eq:                                18
% 3.67/1.05  fd_pure:                                0
% 3.67/1.05  fd_pseudo:                              0
% 3.67/1.05  fd_cond:                                0
% 3.67/1.05  fd_pseudo_cond:                         2
% 3.67/1.05  ac_symbols:                             0
% 3.67/1.05  
% 3.67/1.05  ------ Propositional Solver
% 3.67/1.05  
% 3.67/1.05  prop_solver_calls:                      28
% 3.67/1.05  prop_fast_solver_calls:                 2132
% 3.67/1.05  smt_solver_calls:                       0
% 3.67/1.05  smt_fast_solver_calls:                  0
% 3.67/1.05  prop_num_of_clauses:                    4214
% 3.67/1.05  prop_preprocess_simplified:             10922
% 3.67/1.05  prop_fo_subsumed:                       100
% 3.67/1.05  prop_solver_time:                       0.
% 3.67/1.05  smt_solver_time:                        0.
% 3.67/1.05  smt_fast_solver_time:                   0.
% 3.67/1.05  prop_fast_solver_time:                  0.
% 3.67/1.05  prop_unsat_core_time:                   0.
% 3.67/1.05  
% 3.67/1.05  ------ QBF
% 3.67/1.05  
% 3.67/1.05  qbf_q_res:                              0
% 3.67/1.05  qbf_num_tautologies:                    0
% 3.67/1.05  qbf_prep_cycles:                        0
% 3.67/1.05  
% 3.67/1.05  ------ BMC1
% 3.67/1.05  
% 3.67/1.05  bmc1_current_bound:                     -1
% 3.67/1.05  bmc1_last_solved_bound:                 -1
% 3.67/1.05  bmc1_unsat_core_size:                   -1
% 3.67/1.05  bmc1_unsat_core_parents_size:           -1
% 3.67/1.05  bmc1_merge_next_fun:                    0
% 3.67/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.67/1.05  
% 3.67/1.05  ------ Instantiation
% 3.67/1.05  
% 3.67/1.05  inst_num_of_clauses:                    1020
% 3.67/1.05  inst_num_in_passive:                    147
% 3.67/1.05  inst_num_in_active:                     514
% 3.67/1.05  inst_num_in_unprocessed:                359
% 3.67/1.05  inst_num_of_loops:                      600
% 3.67/1.05  inst_num_of_learning_restarts:          0
% 3.67/1.05  inst_num_moves_active_passive:          85
% 3.67/1.05  inst_lit_activity:                      0
% 3.67/1.05  inst_lit_activity_moves:                1
% 3.67/1.05  inst_num_tautologies:                   0
% 3.67/1.05  inst_num_prop_implied:                  0
% 3.67/1.05  inst_num_existing_simplified:           0
% 3.67/1.05  inst_num_eq_res_simplified:             0
% 3.67/1.05  inst_num_child_elim:                    0
% 3.67/1.05  inst_num_of_dismatching_blockings:      100
% 3.67/1.05  inst_num_of_non_proper_insts:           1063
% 3.67/1.05  inst_num_of_duplicates:                 0
% 3.67/1.05  inst_inst_num_from_inst_to_res:         0
% 3.67/1.05  inst_dismatching_checking_time:         0.
% 3.67/1.05  
% 3.67/1.05  ------ Resolution
% 3.67/1.05  
% 3.67/1.05  res_num_of_clauses:                     0
% 3.67/1.05  res_num_in_passive:                     0
% 3.67/1.05  res_num_in_active:                      0
% 3.67/1.05  res_num_of_loops:                       198
% 3.67/1.05  res_forward_subset_subsumed:            17
% 3.67/1.05  res_backward_subset_subsumed:           0
% 3.67/1.05  res_forward_subsumed:                   0
% 3.67/1.05  res_backward_subsumed:                  0
% 3.67/1.05  res_forward_subsumption_resolution:     1
% 3.67/1.05  res_backward_subsumption_resolution:    0
% 3.67/1.05  res_clause_to_clause_subsumption:       474
% 3.67/1.05  res_orphan_elimination:                 0
% 3.67/1.05  res_tautology_del:                      46
% 3.67/1.05  res_num_eq_res_simplified:              0
% 3.67/1.05  res_num_sel_changes:                    0
% 3.67/1.05  res_moves_from_active_to_pass:          0
% 3.67/1.05  
% 3.67/1.05  ------ Superposition
% 3.67/1.05  
% 3.67/1.05  sup_time_total:                         0.
% 3.67/1.05  sup_time_generating:                    0.
% 3.67/1.05  sup_time_sim_full:                      0.
% 3.67/1.05  sup_time_sim_immed:                     0.
% 3.67/1.05  
% 3.67/1.05  sup_num_of_clauses:                     185
% 3.67/1.05  sup_num_in_active:                      116
% 3.67/1.05  sup_num_in_passive:                     69
% 3.67/1.05  sup_num_of_loops:                       118
% 3.67/1.05  sup_fw_superposition:                   133
% 3.67/1.05  sup_bw_superposition:                   62
% 3.67/1.05  sup_immediate_simplified:               87
% 3.67/1.05  sup_given_eliminated:                   0
% 3.67/1.05  comparisons_done:                       0
% 3.67/1.05  comparisons_avoided:                    0
% 3.67/1.05  
% 3.67/1.05  ------ Simplifications
% 3.67/1.05  
% 3.67/1.05  
% 3.67/1.05  sim_fw_subset_subsumed:                 8
% 3.67/1.05  sim_bw_subset_subsumed:                 0
% 3.67/1.05  sim_fw_subsumed:                        6
% 3.67/1.05  sim_bw_subsumed:                        2
% 3.67/1.05  sim_fw_subsumption_res:                 0
% 3.67/1.05  sim_bw_subsumption_res:                 0
% 3.67/1.05  sim_tautology_del:                      2
% 3.67/1.05  sim_eq_tautology_del:                   1
% 3.67/1.05  sim_eq_res_simp:                        0
% 3.67/1.05  sim_fw_demodulated:                     46
% 3.67/1.05  sim_bw_demodulated:                     3
% 3.67/1.05  sim_light_normalised:                   42
% 3.67/1.05  sim_joinable_taut:                      0
% 3.67/1.05  sim_joinable_simp:                      0
% 3.67/1.05  sim_ac_normalised:                      0
% 3.67/1.05  sim_smt_subsumption:                    0
% 3.67/1.05  
%------------------------------------------------------------------------------
