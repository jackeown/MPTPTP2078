%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:25 EST 2020

% Result     : Theorem 39.62s
% Output     : CNFRefutation 39.62s
% Verified   : 
% Statistics : Number of formulae       :  279 (7252 expanded)
%              Number of clauses        :  183 (1791 expanded)
%              Number of leaves         :   24 (2757 expanded)
%              Depth                    :   27
%              Number of atoms          : 1395 (86563 expanded)
%              Number of equality atoms :  609 (20201 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f60,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f46,f59,f58,f57,f56,f55,f54])).

fof(f101,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f60])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f99,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f93,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_yellow_1(X1)
      & v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
    ? [X1] :
      ( v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v1_partfun1(sK0(X0),X0)
        & v1_funct_1(sK0(X0))
        & v4_relat_1(sK0(X0),X0)
        & v1_relat_1(sK0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( v1_partfun1(sK0(X0),X0)
      & v1_funct_1(sK0(X0))
      & v4_relat_1(sK0(X0),X0)
      & v1_relat_1(sK0(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f50])).

fof(f79,plain,(
    ! [X0] : v4_relat_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X0] : v1_relat_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X0] : v1_funct_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X0] : v1_partfun1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f60])).

fof(f96,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f97,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f42])).

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
    inference(flattening,[],[f52])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
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
    inference(equality_resolution,[],[f83])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f102,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f60])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f106,plain,(
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
    inference(equality_resolution,[],[f84])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1957,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_598,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_15,c_11,c_10])).

cnf(c_603,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_602])).

cnf(c_1941,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_4859,plain,
    ( k1_relat_1(sK6) = sK4
    | v1_partfun1(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1941])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_43,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_52,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_53,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_54,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2131,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2316,plain,
    ( ~ v1_funct_2(sK6,X0,sK2)
    | v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_2768,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | v1_partfun1(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2316])).

cnf(c_2769,plain,
    ( v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_partfun1(sK6,sK4) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2768])).

cnf(c_5264,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4859,c_43,c_52,c_53,c_54,c_2769])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_540,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_35])).

cnf(c_541,plain,
    ( r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_543,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_39,c_37])).

cnf(c_574,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_relat_1(X0) != sK4
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_543])).

cnf(c_575,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,sK3) = k1_xboole_0
    | k1_relat_1(X0) != sK4 ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_1942,plain,
    ( k7_relat_1(X0,sK3) = k1_xboole_0
    | k1_relat_1(X0) != sK4
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_5269,plain,
    ( k7_relat_1(sK6,sK3) = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5264,c_1942])).

cnf(c_1967,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3748,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1967])).

cnf(c_7169,plain,
    ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5269,c_3748])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1968,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3824,plain,
    ( k1_relat_1(k7_relat_1(sK6,X0)) = k3_xboole_0(k1_relat_1(sK6),X0) ),
    inference(superposition,[status(thm)],[c_3748,c_1968])).

cnf(c_5266,plain,
    ( k1_relat_1(k7_relat_1(sK6,X0)) = k3_xboole_0(sK4,X0) ),
    inference(demodulation,[status(thm)],[c_5264,c_3824])).

cnf(c_7171,plain,
    ( k3_xboole_0(sK4,sK3) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7169,c_5266])).

cnf(c_19,plain,
    ( v4_relat_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_21,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_684,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK0(X1) != X0
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_685,plain,
    ( ~ v1_partfun1(sK0(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(sK0(k1_xboole_0))
    | ~ v1_relat_1(sK0(k1_xboole_0))
    | k1_xboole_0 = sK0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_20,plain,
    ( v1_relat_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_18,plain,
    ( v1_funct_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_17,plain,
    ( v1_partfun1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_695,plain,
    ( k1_xboole_0 = sK0(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_685,c_20,c_18,c_17])).

cnf(c_635,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | sK0(X2) != X0
    | k1_relat_1(X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_636,plain,
    ( ~ v1_partfun1(sK0(X0),X0)
    | ~ v1_relat_1(sK0(X0))
    | k1_relat_1(sK0(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_640,plain,
    ( k1_relat_1(sK0(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_20,c_17])).

cnf(c_3444,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_695,c_640])).

cnf(c_7172,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7171,c_3444])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1954,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4860,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_partfun1(sK5,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1941])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_50,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2321,plain,
    ( ~ v1_funct_2(sK5,X0,sK2)
    | v1_partfun1(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_2322,plain,
    ( v1_funct_2(sK5,X0,sK2) != iProver_top
    | v1_partfun1(sK5,X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2321])).

cnf(c_2324,plain,
    ( v1_funct_2(sK5,sK3,sK2) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_5276,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4860,c_43,c_49,c_50,c_51,c_2324])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_312,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_554,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(X2,X3) != k1_xboole_0
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_312,c_5])).

cnf(c_555,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_1943,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_34616,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | k3_xboole_0(X0,sK3) != k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5276,c_1943])).

cnf(c_3749,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1967])).

cnf(c_34876,plain,
    ( k3_xboole_0(X0,sK3) != k1_xboole_0
    | k7_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34616,c_3749])).

cnf(c_34877,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | k3_xboole_0(X0,sK3) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_34876])).

cnf(c_34879,plain,
    ( k7_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7172,c_34877])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_314,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_569,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_314,c_543])).

cnf(c_570,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1969,plain,
    ( k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4024,plain,
    ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0)) = k7_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_3749,c_1969])).

cnf(c_3827,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(k1_relat_1(sK5),X0) ),
    inference(superposition,[status(thm)],[c_3749,c_1968])).

cnf(c_4025,plain,
    ( k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0))) = k7_relat_1(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_4024,c_3827])).

cnf(c_5278,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_5276,c_3827])).

cnf(c_8262,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK3,X0)) = k7_relat_1(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_4025,c_4025,c_5278])).

cnf(c_8264,plain,
    ( k7_relat_1(sK5,sK4) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_570,c_8262])).

cnf(c_76072,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34879,c_8264])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1965,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4152,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1965])).

cnf(c_4854,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4152,c_49])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1951,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1972,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4058,plain,
    ( k9_subset_1(sK1,X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_1951,c_1972])).

cnf(c_4151,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1965])).

cnf(c_4790,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4151,c_52])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f107])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f86])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_232,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_27,c_26,c_25])).

cnf(c_233,plain,
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
    inference(renaming,[status(thm)],[c_232])).

cnf(c_1945,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_7658,plain,
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
    inference(superposition,[status(thm)],[c_4790,c_1945])).

cnf(c_46,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_15655,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7658,c_43,c_46,c_52,c_53,c_54])).

cnf(c_15656,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_15655])).

cnf(c_15668,plain,
    ( k2_partfun1(X0,sK2,X1,k3_xboole_0(X0,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,X0,sK4))
    | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4058,c_15656])).

cnf(c_15669,plain,
    ( k2_partfun1(X0,sK2,X1,k3_xboole_0(X0,sK4)) != k7_relat_1(sK6,k3_xboole_0(X0,sK4))
    | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15668,c_4058])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_42,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_18397,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | k2_partfun1(X0,sK2,X1,k3_xboole_0(X0,sK4)) != k7_relat_1(sK6,k3_xboole_0(X0,sK4))
    | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15669,c_42,c_47])).

cnf(c_18398,plain,
    ( k2_partfun1(X0,sK2,X1,k3_xboole_0(X0,sK4)) != k7_relat_1(sK6,k3_xboole_0(X0,sK4))
    | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_18397])).

cnf(c_18405,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4854,c_18398])).

cnf(c_4023,plain,
    ( k7_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),X0)) = k7_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_3748,c_1969])).

cnf(c_4026,plain,
    ( k7_relat_1(sK6,k1_relat_1(k7_relat_1(sK6,X0))) = k7_relat_1(sK6,X0) ),
    inference(light_normalisation,[status(thm)],[c_4023,c_3824])).

cnf(c_8640,plain,
    ( k7_relat_1(sK6,k3_xboole_0(sK4,X0)) = k7_relat_1(sK6,X0) ),
    inference(light_normalisation,[status(thm)],[c_4026,c_4026,c_5266])).

cnf(c_13654,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k7_relat_1(sK6,sK3) ),
    inference(superposition,[status(thm)],[c_7172,c_8640])).

cnf(c_13655,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13654,c_7169])).

cnf(c_18422,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18405,c_570,c_13655])).

cnf(c_1958,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
    | v1_xboole_0(X5) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1960,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X5) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5085,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
    | v1_funct_2(X5,X2,X3) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k1_tmap_1(X0,X3,X1,X2,X4,X5)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1960,c_1965])).

cnf(c_9410,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
    | v1_funct_2(X5,X2,X3) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1958,c_5085])).

cnf(c_12361,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_9410])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2023,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2024,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2023])).

cnf(c_13721,plain,
    ( v1_xboole_0(X1) = iProver_top
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12361,c_43,c_46,c_52,c_53,c_2024])).

cnf(c_13722,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_13721])).

cnf(c_13730,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_13722])).

cnf(c_44,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_14205,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13730,c_44,c_49,c_50])).

cnf(c_14211,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1951,c_14205])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_14216,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14211,c_45])).

cnf(c_18423,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18422,c_14216])).

cnf(c_28,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4162,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK4,sK2,sK6,k3_xboole_0(sK3,sK4)) != k2_partfun1(sK3,sK2,sK5,k3_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_4058,c_28])).

cnf(c_4163,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4162,c_570])).

cnf(c_5327,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4163,c_4790,c_4854])).

cnf(c_14220,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_14216,c_5327])).

cnf(c_14221,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14220,c_13655])).

cnf(c_14222,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14221,c_14216])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_239,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_27,c_26,c_25])).

cnf(c_240,plain,
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
    inference(renaming,[status(thm)],[c_239])).

cnf(c_1944,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_7205,plain,
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
    inference(superposition,[status(thm)],[c_4790,c_1944])).

cnf(c_7471,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7205,c_43,c_46,c_52,c_53,c_54])).

cnf(c_7472,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7471])).

cnf(c_7478,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4854,c_7472])).

cnf(c_2065,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2066,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2065])).

cnf(c_7560,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7478,c_44,c_49,c_50,c_51,c_2066])).

cnf(c_7561,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7560])).

cnf(c_7566,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4058,c_7561])).

cnf(c_7567,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7566,c_570])).

cnf(c_7568,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7567,c_4058])).

cnf(c_7569,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7568,c_570])).

cnf(c_7570,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7569])).

cnf(c_7655,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7569,c_38,c_36,c_7570])).

cnf(c_14219,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_14216,c_7655])).

cnf(c_14223,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14219,c_13655])).

cnf(c_15192,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14222,c_14223])).

cnf(c_15663,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4854,c_15656])).

cnf(c_18120,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15663,c_44,c_49,c_50,c_51,c_2066])).

cnf(c_18121,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18120])).

cnf(c_18126,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4058,c_18121])).

cnf(c_18127,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18126,c_570,c_13655])).

cnf(c_18128,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18127,c_4058,c_8262,c_14216])).

cnf(c_18129,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18128,c_8264])).

cnf(c_18130,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18129])).

cnf(c_18448,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18423,c_38,c_36,c_15192,c_18130])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76072,c_18448])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.62/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.62/5.49  
% 39.62/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.62/5.49  
% 39.62/5.49  ------  iProver source info
% 39.62/5.49  
% 39.62/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.62/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.62/5.49  git: non_committed_changes: false
% 39.62/5.49  git: last_make_outside_of_git: false
% 39.62/5.49  
% 39.62/5.49  ------ 
% 39.62/5.49  
% 39.62/5.49  ------ Input Options
% 39.62/5.49  
% 39.62/5.49  --out_options                           all
% 39.62/5.49  --tptp_safe_out                         true
% 39.62/5.49  --problem_path                          ""
% 39.62/5.49  --include_path                          ""
% 39.62/5.49  --clausifier                            res/vclausify_rel
% 39.62/5.49  --clausifier_options                    ""
% 39.62/5.49  --stdin                                 false
% 39.62/5.49  --stats_out                             all
% 39.62/5.49  
% 39.62/5.49  ------ General Options
% 39.62/5.49  
% 39.62/5.49  --fof                                   false
% 39.62/5.49  --time_out_real                         305.
% 39.62/5.49  --time_out_virtual                      -1.
% 39.62/5.49  --symbol_type_check                     false
% 39.62/5.49  --clausify_out                          false
% 39.62/5.49  --sig_cnt_out                           false
% 39.62/5.49  --trig_cnt_out                          false
% 39.62/5.49  --trig_cnt_out_tolerance                1.
% 39.62/5.49  --trig_cnt_out_sk_spl                   false
% 39.62/5.49  --abstr_cl_out                          false
% 39.62/5.49  
% 39.62/5.49  ------ Global Options
% 39.62/5.49  
% 39.62/5.49  --schedule                              default
% 39.62/5.49  --add_important_lit                     false
% 39.62/5.49  --prop_solver_per_cl                    1000
% 39.62/5.49  --min_unsat_core                        false
% 39.62/5.49  --soft_assumptions                      false
% 39.62/5.49  --soft_lemma_size                       3
% 39.62/5.49  --prop_impl_unit_size                   0
% 39.62/5.49  --prop_impl_unit                        []
% 39.62/5.49  --share_sel_clauses                     true
% 39.62/5.49  --reset_solvers                         false
% 39.62/5.49  --bc_imp_inh                            [conj_cone]
% 39.62/5.49  --conj_cone_tolerance                   3.
% 39.62/5.49  --extra_neg_conj                        none
% 39.62/5.49  --large_theory_mode                     true
% 39.62/5.49  --prolific_symb_bound                   200
% 39.62/5.49  --lt_threshold                          2000
% 39.62/5.49  --clause_weak_htbl                      true
% 39.62/5.49  --gc_record_bc_elim                     false
% 39.62/5.49  
% 39.62/5.49  ------ Preprocessing Options
% 39.62/5.49  
% 39.62/5.49  --preprocessing_flag                    true
% 39.62/5.49  --time_out_prep_mult                    0.1
% 39.62/5.49  --splitting_mode                        input
% 39.62/5.49  --splitting_grd                         true
% 39.62/5.49  --splitting_cvd                         false
% 39.62/5.49  --splitting_cvd_svl                     false
% 39.62/5.49  --splitting_nvd                         32
% 39.62/5.49  --sub_typing                            true
% 39.62/5.49  --prep_gs_sim                           true
% 39.62/5.49  --prep_unflatten                        true
% 39.62/5.49  --prep_res_sim                          true
% 39.62/5.49  --prep_upred                            true
% 39.62/5.49  --prep_sem_filter                       exhaustive
% 39.62/5.49  --prep_sem_filter_out                   false
% 39.62/5.49  --pred_elim                             true
% 39.62/5.49  --res_sim_input                         true
% 39.62/5.49  --eq_ax_congr_red                       true
% 39.62/5.49  --pure_diseq_elim                       true
% 39.62/5.49  --brand_transform                       false
% 39.62/5.49  --non_eq_to_eq                          false
% 39.62/5.49  --prep_def_merge                        true
% 39.62/5.49  --prep_def_merge_prop_impl              false
% 39.62/5.49  --prep_def_merge_mbd                    true
% 39.62/5.49  --prep_def_merge_tr_red                 false
% 39.62/5.49  --prep_def_merge_tr_cl                  false
% 39.62/5.49  --smt_preprocessing                     true
% 39.62/5.49  --smt_ac_axioms                         fast
% 39.62/5.49  --preprocessed_out                      false
% 39.62/5.49  --preprocessed_stats                    false
% 39.62/5.49  
% 39.62/5.49  ------ Abstraction refinement Options
% 39.62/5.49  
% 39.62/5.49  --abstr_ref                             []
% 39.62/5.49  --abstr_ref_prep                        false
% 39.62/5.49  --abstr_ref_until_sat                   false
% 39.62/5.49  --abstr_ref_sig_restrict                funpre
% 39.62/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.62/5.49  --abstr_ref_under                       []
% 39.62/5.49  
% 39.62/5.49  ------ SAT Options
% 39.62/5.49  
% 39.62/5.49  --sat_mode                              false
% 39.62/5.49  --sat_fm_restart_options                ""
% 39.62/5.49  --sat_gr_def                            false
% 39.62/5.49  --sat_epr_types                         true
% 39.62/5.49  --sat_non_cyclic_types                  false
% 39.62/5.49  --sat_finite_models                     false
% 39.62/5.49  --sat_fm_lemmas                         false
% 39.62/5.49  --sat_fm_prep                           false
% 39.62/5.49  --sat_fm_uc_incr                        true
% 39.62/5.49  --sat_out_model                         small
% 39.62/5.49  --sat_out_clauses                       false
% 39.62/5.49  
% 39.62/5.49  ------ QBF Options
% 39.62/5.49  
% 39.62/5.49  --qbf_mode                              false
% 39.62/5.49  --qbf_elim_univ                         false
% 39.62/5.49  --qbf_dom_inst                          none
% 39.62/5.49  --qbf_dom_pre_inst                      false
% 39.62/5.49  --qbf_sk_in                             false
% 39.62/5.49  --qbf_pred_elim                         true
% 39.62/5.49  --qbf_split                             512
% 39.62/5.49  
% 39.62/5.49  ------ BMC1 Options
% 39.62/5.49  
% 39.62/5.49  --bmc1_incremental                      false
% 39.62/5.49  --bmc1_axioms                           reachable_all
% 39.62/5.49  --bmc1_min_bound                        0
% 39.62/5.49  --bmc1_max_bound                        -1
% 39.62/5.49  --bmc1_max_bound_default                -1
% 39.62/5.49  --bmc1_symbol_reachability              true
% 39.62/5.49  --bmc1_property_lemmas                  false
% 39.62/5.49  --bmc1_k_induction                      false
% 39.62/5.49  --bmc1_non_equiv_states                 false
% 39.62/5.49  --bmc1_deadlock                         false
% 39.62/5.49  --bmc1_ucm                              false
% 39.62/5.49  --bmc1_add_unsat_core                   none
% 39.62/5.49  --bmc1_unsat_core_children              false
% 39.62/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.62/5.49  --bmc1_out_stat                         full
% 39.62/5.49  --bmc1_ground_init                      false
% 39.62/5.49  --bmc1_pre_inst_next_state              false
% 39.62/5.49  --bmc1_pre_inst_state                   false
% 39.62/5.49  --bmc1_pre_inst_reach_state             false
% 39.62/5.49  --bmc1_out_unsat_core                   false
% 39.62/5.49  --bmc1_aig_witness_out                  false
% 39.62/5.49  --bmc1_verbose                          false
% 39.62/5.49  --bmc1_dump_clauses_tptp                false
% 39.62/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.62/5.49  --bmc1_dump_file                        -
% 39.62/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.62/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.62/5.49  --bmc1_ucm_extend_mode                  1
% 39.62/5.49  --bmc1_ucm_init_mode                    2
% 39.62/5.49  --bmc1_ucm_cone_mode                    none
% 39.62/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.62/5.49  --bmc1_ucm_relax_model                  4
% 39.62/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.62/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.62/5.49  --bmc1_ucm_layered_model                none
% 39.62/5.49  --bmc1_ucm_max_lemma_size               10
% 39.62/5.49  
% 39.62/5.49  ------ AIG Options
% 39.62/5.49  
% 39.62/5.49  --aig_mode                              false
% 39.62/5.49  
% 39.62/5.49  ------ Instantiation Options
% 39.62/5.49  
% 39.62/5.49  --instantiation_flag                    true
% 39.62/5.49  --inst_sos_flag                         true
% 39.62/5.49  --inst_sos_phase                        true
% 39.62/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.62/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.62/5.49  --inst_lit_sel_side                     num_symb
% 39.62/5.49  --inst_solver_per_active                1400
% 39.62/5.49  --inst_solver_calls_frac                1.
% 39.62/5.49  --inst_passive_queue_type               priority_queues
% 39.62/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.62/5.49  --inst_passive_queues_freq              [25;2]
% 39.62/5.49  --inst_dismatching                      true
% 39.62/5.49  --inst_eager_unprocessed_to_passive     true
% 39.62/5.49  --inst_prop_sim_given                   true
% 39.62/5.49  --inst_prop_sim_new                     false
% 39.62/5.49  --inst_subs_new                         false
% 39.62/5.49  --inst_eq_res_simp                      false
% 39.62/5.49  --inst_subs_given                       false
% 39.62/5.49  --inst_orphan_elimination               true
% 39.62/5.49  --inst_learning_loop_flag               true
% 39.62/5.49  --inst_learning_start                   3000
% 39.62/5.49  --inst_learning_factor                  2
% 39.62/5.49  --inst_start_prop_sim_after_learn       3
% 39.62/5.49  --inst_sel_renew                        solver
% 39.62/5.49  --inst_lit_activity_flag                true
% 39.62/5.49  --inst_restr_to_given                   false
% 39.62/5.49  --inst_activity_threshold               500
% 39.62/5.49  --inst_out_proof                        true
% 39.62/5.49  
% 39.62/5.49  ------ Resolution Options
% 39.62/5.49  
% 39.62/5.49  --resolution_flag                       true
% 39.62/5.49  --res_lit_sel                           adaptive
% 39.62/5.49  --res_lit_sel_side                      none
% 39.62/5.49  --res_ordering                          kbo
% 39.62/5.49  --res_to_prop_solver                    active
% 39.62/5.49  --res_prop_simpl_new                    false
% 39.62/5.49  --res_prop_simpl_given                  true
% 39.62/5.49  --res_passive_queue_type                priority_queues
% 39.62/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.62/5.49  --res_passive_queues_freq               [15;5]
% 39.62/5.49  --res_forward_subs                      full
% 39.62/5.49  --res_backward_subs                     full
% 39.62/5.49  --res_forward_subs_resolution           true
% 39.62/5.49  --res_backward_subs_resolution          true
% 39.62/5.49  --res_orphan_elimination                true
% 39.62/5.49  --res_time_limit                        2.
% 39.62/5.49  --res_out_proof                         true
% 39.62/5.49  
% 39.62/5.49  ------ Superposition Options
% 39.62/5.49  
% 39.62/5.49  --superposition_flag                    true
% 39.62/5.49  --sup_passive_queue_type                priority_queues
% 39.62/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.62/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.62/5.49  --demod_completeness_check              fast
% 39.62/5.49  --demod_use_ground                      true
% 39.62/5.49  --sup_to_prop_solver                    passive
% 39.62/5.49  --sup_prop_simpl_new                    true
% 39.62/5.49  --sup_prop_simpl_given                  true
% 39.62/5.49  --sup_fun_splitting                     true
% 39.62/5.49  --sup_smt_interval                      50000
% 39.62/5.49  
% 39.62/5.49  ------ Superposition Simplification Setup
% 39.62/5.49  
% 39.62/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.62/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.62/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.62/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.62/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.62/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.62/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.62/5.49  --sup_immed_triv                        [TrivRules]
% 39.62/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.49  --sup_immed_bw_main                     []
% 39.62/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.62/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.62/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.49  --sup_input_bw                          []
% 39.62/5.49  
% 39.62/5.49  ------ Combination Options
% 39.62/5.49  
% 39.62/5.49  --comb_res_mult                         3
% 39.62/5.49  --comb_sup_mult                         2
% 39.62/5.49  --comb_inst_mult                        10
% 39.62/5.49  
% 39.62/5.49  ------ Debug Options
% 39.62/5.49  
% 39.62/5.49  --dbg_backtrace                         false
% 39.62/5.49  --dbg_dump_prop_clauses                 false
% 39.62/5.49  --dbg_dump_prop_clauses_file            -
% 39.62/5.49  --dbg_out_stat                          false
% 39.62/5.49  ------ Parsing...
% 39.62/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.62/5.49  
% 39.62/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 39.62/5.49  
% 39.62/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.62/5.49  
% 39.62/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.62/5.49  ------ Proving...
% 39.62/5.49  ------ Problem Properties 
% 39.62/5.49  
% 39.62/5.49  
% 39.62/5.49  clauses                                 39
% 39.62/5.49  conjectures                             13
% 39.62/5.49  EPR                                     8
% 39.62/5.49  Horn                                    32
% 39.62/5.49  unary                                   20
% 39.62/5.49  binary                                  5
% 39.62/5.49  lits                                    141
% 39.62/5.49  lits eq                                 22
% 39.62/5.49  fd_pure                                 0
% 39.62/5.49  fd_pseudo                               0
% 39.62/5.49  fd_cond                                 1
% 39.62/5.49  fd_pseudo_cond                          1
% 39.62/5.49  AC symbols                              0
% 39.62/5.49  
% 39.62/5.49  ------ Schedule dynamic 5 is on 
% 39.62/5.49  
% 39.62/5.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.62/5.49  
% 39.62/5.49  
% 39.62/5.49  ------ 
% 39.62/5.49  Current options:
% 39.62/5.49  ------ 
% 39.62/5.49  
% 39.62/5.49  ------ Input Options
% 39.62/5.49  
% 39.62/5.49  --out_options                           all
% 39.62/5.49  --tptp_safe_out                         true
% 39.62/5.49  --problem_path                          ""
% 39.62/5.49  --include_path                          ""
% 39.62/5.49  --clausifier                            res/vclausify_rel
% 39.62/5.49  --clausifier_options                    ""
% 39.62/5.49  --stdin                                 false
% 39.62/5.49  --stats_out                             all
% 39.62/5.49  
% 39.62/5.49  ------ General Options
% 39.62/5.49  
% 39.62/5.49  --fof                                   false
% 39.62/5.49  --time_out_real                         305.
% 39.62/5.49  --time_out_virtual                      -1.
% 39.62/5.49  --symbol_type_check                     false
% 39.62/5.49  --clausify_out                          false
% 39.62/5.49  --sig_cnt_out                           false
% 39.62/5.49  --trig_cnt_out                          false
% 39.62/5.49  --trig_cnt_out_tolerance                1.
% 39.62/5.49  --trig_cnt_out_sk_spl                   false
% 39.62/5.49  --abstr_cl_out                          false
% 39.62/5.49  
% 39.62/5.49  ------ Global Options
% 39.62/5.49  
% 39.62/5.49  --schedule                              default
% 39.62/5.49  --add_important_lit                     false
% 39.62/5.49  --prop_solver_per_cl                    1000
% 39.62/5.49  --min_unsat_core                        false
% 39.62/5.49  --soft_assumptions                      false
% 39.62/5.49  --soft_lemma_size                       3
% 39.62/5.49  --prop_impl_unit_size                   0
% 39.62/5.49  --prop_impl_unit                        []
% 39.62/5.49  --share_sel_clauses                     true
% 39.62/5.49  --reset_solvers                         false
% 39.62/5.49  --bc_imp_inh                            [conj_cone]
% 39.62/5.49  --conj_cone_tolerance                   3.
% 39.62/5.49  --extra_neg_conj                        none
% 39.62/5.49  --large_theory_mode                     true
% 39.62/5.49  --prolific_symb_bound                   200
% 39.62/5.49  --lt_threshold                          2000
% 39.62/5.49  --clause_weak_htbl                      true
% 39.62/5.49  --gc_record_bc_elim                     false
% 39.62/5.49  
% 39.62/5.49  ------ Preprocessing Options
% 39.62/5.49  
% 39.62/5.49  --preprocessing_flag                    true
% 39.62/5.49  --time_out_prep_mult                    0.1
% 39.62/5.49  --splitting_mode                        input
% 39.62/5.49  --splitting_grd                         true
% 39.62/5.49  --splitting_cvd                         false
% 39.62/5.49  --splitting_cvd_svl                     false
% 39.62/5.49  --splitting_nvd                         32
% 39.62/5.49  --sub_typing                            true
% 39.62/5.49  --prep_gs_sim                           true
% 39.62/5.49  --prep_unflatten                        true
% 39.62/5.49  --prep_res_sim                          true
% 39.62/5.49  --prep_upred                            true
% 39.62/5.49  --prep_sem_filter                       exhaustive
% 39.62/5.49  --prep_sem_filter_out                   false
% 39.62/5.49  --pred_elim                             true
% 39.62/5.49  --res_sim_input                         true
% 39.62/5.49  --eq_ax_congr_red                       true
% 39.62/5.49  --pure_diseq_elim                       true
% 39.62/5.49  --brand_transform                       false
% 39.62/5.49  --non_eq_to_eq                          false
% 39.62/5.49  --prep_def_merge                        true
% 39.62/5.49  --prep_def_merge_prop_impl              false
% 39.62/5.49  --prep_def_merge_mbd                    true
% 39.62/5.49  --prep_def_merge_tr_red                 false
% 39.62/5.49  --prep_def_merge_tr_cl                  false
% 39.62/5.49  --smt_preprocessing                     true
% 39.62/5.49  --smt_ac_axioms                         fast
% 39.62/5.49  --preprocessed_out                      false
% 39.62/5.49  --preprocessed_stats                    false
% 39.62/5.49  
% 39.62/5.49  ------ Abstraction refinement Options
% 39.62/5.49  
% 39.62/5.49  --abstr_ref                             []
% 39.62/5.49  --abstr_ref_prep                        false
% 39.62/5.49  --abstr_ref_until_sat                   false
% 39.62/5.49  --abstr_ref_sig_restrict                funpre
% 39.62/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.62/5.49  --abstr_ref_under                       []
% 39.62/5.49  
% 39.62/5.49  ------ SAT Options
% 39.62/5.49  
% 39.62/5.49  --sat_mode                              false
% 39.62/5.49  --sat_fm_restart_options                ""
% 39.62/5.49  --sat_gr_def                            false
% 39.62/5.49  --sat_epr_types                         true
% 39.62/5.49  --sat_non_cyclic_types                  false
% 39.62/5.49  --sat_finite_models                     false
% 39.62/5.49  --sat_fm_lemmas                         false
% 39.62/5.49  --sat_fm_prep                           false
% 39.62/5.49  --sat_fm_uc_incr                        true
% 39.62/5.49  --sat_out_model                         small
% 39.62/5.49  --sat_out_clauses                       false
% 39.62/5.49  
% 39.62/5.49  ------ QBF Options
% 39.62/5.49  
% 39.62/5.49  --qbf_mode                              false
% 39.62/5.49  --qbf_elim_univ                         false
% 39.62/5.49  --qbf_dom_inst                          none
% 39.62/5.49  --qbf_dom_pre_inst                      false
% 39.62/5.49  --qbf_sk_in                             false
% 39.62/5.49  --qbf_pred_elim                         true
% 39.62/5.49  --qbf_split                             512
% 39.62/5.49  
% 39.62/5.49  ------ BMC1 Options
% 39.62/5.49  
% 39.62/5.49  --bmc1_incremental                      false
% 39.62/5.49  --bmc1_axioms                           reachable_all
% 39.62/5.49  --bmc1_min_bound                        0
% 39.62/5.49  --bmc1_max_bound                        -1
% 39.62/5.49  --bmc1_max_bound_default                -1
% 39.62/5.49  --bmc1_symbol_reachability              true
% 39.62/5.49  --bmc1_property_lemmas                  false
% 39.62/5.49  --bmc1_k_induction                      false
% 39.62/5.49  --bmc1_non_equiv_states                 false
% 39.62/5.49  --bmc1_deadlock                         false
% 39.62/5.49  --bmc1_ucm                              false
% 39.62/5.49  --bmc1_add_unsat_core                   none
% 39.62/5.49  --bmc1_unsat_core_children              false
% 39.62/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.62/5.49  --bmc1_out_stat                         full
% 39.62/5.49  --bmc1_ground_init                      false
% 39.62/5.49  --bmc1_pre_inst_next_state              false
% 39.62/5.49  --bmc1_pre_inst_state                   false
% 39.62/5.49  --bmc1_pre_inst_reach_state             false
% 39.62/5.49  --bmc1_out_unsat_core                   false
% 39.62/5.49  --bmc1_aig_witness_out                  false
% 39.62/5.49  --bmc1_verbose                          false
% 39.62/5.49  --bmc1_dump_clauses_tptp                false
% 39.62/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.62/5.49  --bmc1_dump_file                        -
% 39.62/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.62/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.62/5.49  --bmc1_ucm_extend_mode                  1
% 39.62/5.49  --bmc1_ucm_init_mode                    2
% 39.62/5.49  --bmc1_ucm_cone_mode                    none
% 39.62/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.62/5.49  --bmc1_ucm_relax_model                  4
% 39.62/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.62/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.62/5.49  --bmc1_ucm_layered_model                none
% 39.62/5.49  --bmc1_ucm_max_lemma_size               10
% 39.62/5.49  
% 39.62/5.49  ------ AIG Options
% 39.62/5.49  
% 39.62/5.49  --aig_mode                              false
% 39.62/5.49  
% 39.62/5.49  ------ Instantiation Options
% 39.62/5.49  
% 39.62/5.49  --instantiation_flag                    true
% 39.62/5.49  --inst_sos_flag                         true
% 39.62/5.49  --inst_sos_phase                        true
% 39.62/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.62/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.62/5.49  --inst_lit_sel_side                     none
% 39.62/5.49  --inst_solver_per_active                1400
% 39.62/5.49  --inst_solver_calls_frac                1.
% 39.62/5.49  --inst_passive_queue_type               priority_queues
% 39.62/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.62/5.49  --inst_passive_queues_freq              [25;2]
% 39.62/5.49  --inst_dismatching                      true
% 39.62/5.49  --inst_eager_unprocessed_to_passive     true
% 39.62/5.49  --inst_prop_sim_given                   true
% 39.62/5.49  --inst_prop_sim_new                     false
% 39.62/5.49  --inst_subs_new                         false
% 39.62/5.49  --inst_eq_res_simp                      false
% 39.62/5.49  --inst_subs_given                       false
% 39.62/5.49  --inst_orphan_elimination               true
% 39.62/5.49  --inst_learning_loop_flag               true
% 39.62/5.49  --inst_learning_start                   3000
% 39.62/5.49  --inst_learning_factor                  2
% 39.62/5.49  --inst_start_prop_sim_after_learn       3
% 39.62/5.49  --inst_sel_renew                        solver
% 39.62/5.49  --inst_lit_activity_flag                true
% 39.62/5.49  --inst_restr_to_given                   false
% 39.62/5.49  --inst_activity_threshold               500
% 39.62/5.49  --inst_out_proof                        true
% 39.62/5.49  
% 39.62/5.49  ------ Resolution Options
% 39.62/5.49  
% 39.62/5.49  --resolution_flag                       false
% 39.62/5.49  --res_lit_sel                           adaptive
% 39.62/5.49  --res_lit_sel_side                      none
% 39.62/5.49  --res_ordering                          kbo
% 39.62/5.49  --res_to_prop_solver                    active
% 39.62/5.49  --res_prop_simpl_new                    false
% 39.62/5.49  --res_prop_simpl_given                  true
% 39.62/5.49  --res_passive_queue_type                priority_queues
% 39.62/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.62/5.49  --res_passive_queues_freq               [15;5]
% 39.62/5.49  --res_forward_subs                      full
% 39.62/5.49  --res_backward_subs                     full
% 39.62/5.49  --res_forward_subs_resolution           true
% 39.62/5.49  --res_backward_subs_resolution          true
% 39.62/5.49  --res_orphan_elimination                true
% 39.62/5.49  --res_time_limit                        2.
% 39.62/5.49  --res_out_proof                         true
% 39.62/5.49  
% 39.62/5.49  ------ Superposition Options
% 39.62/5.49  
% 39.62/5.49  --superposition_flag                    true
% 39.62/5.49  --sup_passive_queue_type                priority_queues
% 39.62/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.62/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.62/5.49  --demod_completeness_check              fast
% 39.62/5.49  --demod_use_ground                      true
% 39.62/5.49  --sup_to_prop_solver                    passive
% 39.62/5.49  --sup_prop_simpl_new                    true
% 39.62/5.49  --sup_prop_simpl_given                  true
% 39.62/5.49  --sup_fun_splitting                     true
% 39.62/5.49  --sup_smt_interval                      50000
% 39.62/5.49  
% 39.62/5.49  ------ Superposition Simplification Setup
% 39.62/5.49  
% 39.62/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.62/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.62/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.62/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.62/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.62/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.62/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.62/5.49  --sup_immed_triv                        [TrivRules]
% 39.62/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.49  --sup_immed_bw_main                     []
% 39.62/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.62/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.62/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.49  --sup_input_bw                          []
% 39.62/5.49  
% 39.62/5.49  ------ Combination Options
% 39.62/5.49  
% 39.62/5.49  --comb_res_mult                         3
% 39.62/5.49  --comb_sup_mult                         2
% 39.62/5.49  --comb_inst_mult                        10
% 39.62/5.49  
% 39.62/5.49  ------ Debug Options
% 39.62/5.49  
% 39.62/5.49  --dbg_backtrace                         false
% 39.62/5.49  --dbg_dump_prop_clauses                 false
% 39.62/5.49  --dbg_dump_prop_clauses_file            -
% 39.62/5.49  --dbg_out_stat                          false
% 39.62/5.49  
% 39.62/5.49  
% 39.62/5.49  
% 39.62/5.49  
% 39.62/5.49  ------ Proving...
% 39.62/5.49  
% 39.62/5.49  
% 39.62/5.49  % SZS status Theorem for theBenchmark.p
% 39.62/5.49  
% 39.62/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.62/5.49  
% 39.62/5.49  fof(f19,conjecture,(
% 39.62/5.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f20,negated_conjecture,(
% 39.62/5.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 39.62/5.49    inference(negated_conjecture,[],[f19])).
% 39.62/5.49  
% 39.62/5.49  fof(f45,plain,(
% 39.62/5.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 39.62/5.49    inference(ennf_transformation,[],[f20])).
% 39.62/5.49  
% 39.62/5.49  fof(f46,plain,(
% 39.62/5.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 39.62/5.49    inference(flattening,[],[f45])).
% 39.62/5.49  
% 39.62/5.49  fof(f59,plain,(
% 39.62/5.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 39.62/5.49    introduced(choice_axiom,[])).
% 39.62/5.49  
% 39.62/5.49  fof(f58,plain,(
% 39.62/5.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 39.62/5.49    introduced(choice_axiom,[])).
% 39.62/5.49  
% 39.62/5.49  fof(f57,plain,(
% 39.62/5.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 39.62/5.49    introduced(choice_axiom,[])).
% 39.62/5.49  
% 39.62/5.49  fof(f56,plain,(
% 39.62/5.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 39.62/5.49    introduced(choice_axiom,[])).
% 39.62/5.49  
% 39.62/5.49  fof(f55,plain,(
% 39.62/5.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 39.62/5.49    introduced(choice_axiom,[])).
% 39.62/5.49  
% 39.62/5.49  fof(f54,plain,(
% 39.62/5.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 39.62/5.49    introduced(choice_axiom,[])).
% 39.62/5.49  
% 39.62/5.49  fof(f60,plain,(
% 39.62/5.49    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 39.62/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f46,f59,f58,f57,f56,f55,f54])).
% 39.62/5.49  
% 39.62/5.49  fof(f101,plain,(
% 39.62/5.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f11,axiom,(
% 39.62/5.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f22,plain,(
% 39.62/5.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 39.62/5.49    inference(pure_predicate_removal,[],[f11])).
% 39.62/5.49  
% 39.62/5.49  fof(f32,plain,(
% 39.62/5.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.62/5.49    inference(ennf_transformation,[],[f22])).
% 39.62/5.49  
% 39.62/5.49  fof(f72,plain,(
% 39.62/5.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.62/5.49    inference(cnf_transformation,[],[f32])).
% 39.62/5.49  
% 39.62/5.49  fof(f13,axiom,(
% 39.62/5.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f35,plain,(
% 39.62/5.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 39.62/5.49    inference(ennf_transformation,[],[f13])).
% 39.62/5.49  
% 39.62/5.49  fof(f36,plain,(
% 39.62/5.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 39.62/5.49    inference(flattening,[],[f35])).
% 39.62/5.49  
% 39.62/5.49  fof(f49,plain,(
% 39.62/5.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 39.62/5.49    inference(nnf_transformation,[],[f36])).
% 39.62/5.49  
% 39.62/5.49  fof(f75,plain,(
% 39.62/5.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f49])).
% 39.62/5.49  
% 39.62/5.49  fof(f10,axiom,(
% 39.62/5.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f31,plain,(
% 39.62/5.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.62/5.49    inference(ennf_transformation,[],[f10])).
% 39.62/5.49  
% 39.62/5.49  fof(f71,plain,(
% 39.62/5.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.62/5.49    inference(cnf_transformation,[],[f31])).
% 39.62/5.49  
% 39.62/5.49  fof(f90,plain,(
% 39.62/5.49    ~v1_xboole_0(sK2)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f99,plain,(
% 39.62/5.49    v1_funct_1(sK6)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f100,plain,(
% 39.62/5.49    v1_funct_2(sK6,sK4,sK2)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f12,axiom,(
% 39.62/5.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f33,plain,(
% 39.62/5.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 39.62/5.49    inference(ennf_transformation,[],[f12])).
% 39.62/5.49  
% 39.62/5.49  fof(f34,plain,(
% 39.62/5.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 39.62/5.49    inference(flattening,[],[f33])).
% 39.62/5.49  
% 39.62/5.49  fof(f74,plain,(
% 39.62/5.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f34])).
% 39.62/5.49  
% 39.62/5.49  fof(f6,axiom,(
% 39.62/5.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f26,plain,(
% 39.62/5.49    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 39.62/5.49    inference(ennf_transformation,[],[f6])).
% 39.62/5.49  
% 39.62/5.49  fof(f66,plain,(
% 39.62/5.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f26])).
% 39.62/5.49  
% 39.62/5.49  fof(f9,axiom,(
% 39.62/5.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f29,plain,(
% 39.62/5.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 39.62/5.49    inference(ennf_transformation,[],[f9])).
% 39.62/5.49  
% 39.62/5.49  fof(f30,plain,(
% 39.62/5.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 39.62/5.49    inference(flattening,[],[f29])).
% 39.62/5.49  
% 39.62/5.49  fof(f48,plain,(
% 39.62/5.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 39.62/5.49    inference(nnf_transformation,[],[f30])).
% 39.62/5.49  
% 39.62/5.49  fof(f69,plain,(
% 39.62/5.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f48])).
% 39.62/5.49  
% 39.62/5.49  fof(f95,plain,(
% 39.62/5.49    r1_subset_1(sK3,sK4)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f91,plain,(
% 39.62/5.49    ~v1_xboole_0(sK3)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f93,plain,(
% 39.62/5.49    ~v1_xboole_0(sK4)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f8,axiom,(
% 39.62/5.49    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f28,plain,(
% 39.62/5.49    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 39.62/5.49    inference(ennf_transformation,[],[f8])).
% 39.62/5.49  
% 39.62/5.49  fof(f68,plain,(
% 39.62/5.49    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f28])).
% 39.62/5.49  
% 39.62/5.49  fof(f15,axiom,(
% 39.62/5.49    ! [X0] : ? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f21,plain,(
% 39.62/5.49    ! [X0] : ? [X1] : (v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 39.62/5.49    inference(pure_predicate_removal,[],[f15])).
% 39.62/5.49  
% 39.62/5.49  fof(f50,plain,(
% 39.62/5.49    ! [X0] : (? [X1] : (v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(sK0(X0),X0) & v1_funct_1(sK0(X0)) & v4_relat_1(sK0(X0),X0) & v1_relat_1(sK0(X0))))),
% 39.62/5.49    introduced(choice_axiom,[])).
% 39.62/5.49  
% 39.62/5.49  fof(f51,plain,(
% 39.62/5.49    ! [X0] : (v1_partfun1(sK0(X0),X0) & v1_funct_1(sK0(X0)) & v4_relat_1(sK0(X0),X0) & v1_relat_1(sK0(X0)))),
% 39.62/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f50])).
% 39.62/5.49  
% 39.62/5.49  fof(f79,plain,(
% 39.62/5.49    ( ! [X0] : (v4_relat_1(sK0(X0),X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f51])).
% 39.62/5.49  
% 39.62/5.49  fof(f16,axiom,(
% 39.62/5.49    ! [X0] : ((v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k1_xboole_0 = X0)),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f39,plain,(
% 39.62/5.49    ! [X0] : (k1_xboole_0 = X0 | (~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 39.62/5.49    inference(ennf_transformation,[],[f16])).
% 39.62/5.49  
% 39.62/5.49  fof(f40,plain,(
% 39.62/5.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 39.62/5.49    inference(flattening,[],[f39])).
% 39.62/5.49  
% 39.62/5.49  fof(f82,plain,(
% 39.62/5.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f40])).
% 39.62/5.49  
% 39.62/5.49  fof(f78,plain,(
% 39.62/5.49    ( ! [X0] : (v1_relat_1(sK0(X0))) )),
% 39.62/5.49    inference(cnf_transformation,[],[f51])).
% 39.62/5.49  
% 39.62/5.49  fof(f80,plain,(
% 39.62/5.49    ( ! [X0] : (v1_funct_1(sK0(X0))) )),
% 39.62/5.49    inference(cnf_transformation,[],[f51])).
% 39.62/5.49  
% 39.62/5.49  fof(f81,plain,(
% 39.62/5.49    ( ! [X0] : (v1_partfun1(sK0(X0),X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f51])).
% 39.62/5.49  
% 39.62/5.49  fof(f98,plain,(
% 39.62/5.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f96,plain,(
% 39.62/5.49    v1_funct_1(sK5)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f97,plain,(
% 39.62/5.49    v1_funct_2(sK5,sK3,sK2)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f1,axiom,(
% 39.62/5.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f47,plain,(
% 39.62/5.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 39.62/5.49    inference(nnf_transformation,[],[f1])).
% 39.62/5.49  
% 39.62/5.49  fof(f62,plain,(
% 39.62/5.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 39.62/5.49    inference(cnf_transformation,[],[f47])).
% 39.62/5.49  
% 39.62/5.49  fof(f61,plain,(
% 39.62/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f47])).
% 39.62/5.49  
% 39.62/5.49  fof(f7,axiom,(
% 39.62/5.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f27,plain,(
% 39.62/5.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 39.62/5.49    inference(ennf_transformation,[],[f7])).
% 39.62/5.49  
% 39.62/5.49  fof(f67,plain,(
% 39.62/5.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f27])).
% 39.62/5.49  
% 39.62/5.49  fof(f14,axiom,(
% 39.62/5.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f37,plain,(
% 39.62/5.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 39.62/5.49    inference(ennf_transformation,[],[f14])).
% 39.62/5.49  
% 39.62/5.49  fof(f38,plain,(
% 39.62/5.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 39.62/5.49    inference(flattening,[],[f37])).
% 39.62/5.49  
% 39.62/5.49  fof(f77,plain,(
% 39.62/5.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f38])).
% 39.62/5.49  
% 39.62/5.49  fof(f94,plain,(
% 39.62/5.49    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f2,axiom,(
% 39.62/5.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f24,plain,(
% 39.62/5.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 39.62/5.49    inference(ennf_transformation,[],[f2])).
% 39.62/5.49  
% 39.62/5.49  fof(f63,plain,(
% 39.62/5.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 39.62/5.49    inference(cnf_transformation,[],[f24])).
% 39.62/5.49  
% 39.62/5.49  fof(f17,axiom,(
% 39.62/5.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f41,plain,(
% 39.62/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 39.62/5.49    inference(ennf_transformation,[],[f17])).
% 39.62/5.49  
% 39.62/5.49  fof(f42,plain,(
% 39.62/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 39.62/5.49    inference(flattening,[],[f41])).
% 39.62/5.49  
% 39.62/5.49  fof(f52,plain,(
% 39.62/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 39.62/5.49    inference(nnf_transformation,[],[f42])).
% 39.62/5.49  
% 39.62/5.49  fof(f53,plain,(
% 39.62/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 39.62/5.49    inference(flattening,[],[f52])).
% 39.62/5.49  
% 39.62/5.49  fof(f83,plain,(
% 39.62/5.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f53])).
% 39.62/5.49  
% 39.62/5.49  fof(f107,plain,(
% 39.62/5.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.62/5.49    inference(equality_resolution,[],[f83])).
% 39.62/5.49  
% 39.62/5.49  fof(f18,axiom,(
% 39.62/5.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f43,plain,(
% 39.62/5.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 39.62/5.49    inference(ennf_transformation,[],[f18])).
% 39.62/5.49  
% 39.62/5.49  fof(f44,plain,(
% 39.62/5.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 39.62/5.49    inference(flattening,[],[f43])).
% 39.62/5.49  
% 39.62/5.49  fof(f86,plain,(
% 39.62/5.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f44])).
% 39.62/5.49  
% 39.62/5.49  fof(f87,plain,(
% 39.62/5.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f44])).
% 39.62/5.49  
% 39.62/5.49  fof(f88,plain,(
% 39.62/5.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f44])).
% 39.62/5.49  
% 39.62/5.49  fof(f89,plain,(
% 39.62/5.49    ~v1_xboole_0(sK1)),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f4,axiom,(
% 39.62/5.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 39.62/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.49  
% 39.62/5.49  fof(f25,plain,(
% 39.62/5.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 39.62/5.49    inference(ennf_transformation,[],[f4])).
% 39.62/5.49  
% 39.62/5.49  fof(f65,plain,(
% 39.62/5.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f25])).
% 39.62/5.49  
% 39.62/5.49  fof(f92,plain,(
% 39.62/5.49    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f102,plain,(
% 39.62/5.49    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 39.62/5.49    inference(cnf_transformation,[],[f60])).
% 39.62/5.49  
% 39.62/5.49  fof(f84,plain,(
% 39.62/5.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.62/5.49    inference(cnf_transformation,[],[f53])).
% 39.62/5.49  
% 39.62/5.49  fof(f106,plain,(
% 39.62/5.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.62/5.49    inference(equality_resolution,[],[f84])).
% 39.62/5.49  
% 39.62/5.49  cnf(c_29,negated_conjecture,
% 39.62/5.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 39.62/5.49      inference(cnf_transformation,[],[f101]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1957,plain,
% 39.62/5.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_11,plain,
% 39.62/5.49      ( v4_relat_1(X0,X1)
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 39.62/5.49      inference(cnf_transformation,[],[f72]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_15,plain,
% 39.62/5.49      ( ~ v1_partfun1(X0,X1)
% 39.62/5.49      | ~ v4_relat_1(X0,X1)
% 39.62/5.49      | ~ v1_relat_1(X0)
% 39.62/5.49      | k1_relat_1(X0) = X1 ),
% 39.62/5.49      inference(cnf_transformation,[],[f75]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_598,plain,
% 39.62/5.49      ( ~ v1_partfun1(X0,X1)
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ v1_relat_1(X0)
% 39.62/5.49      | k1_relat_1(X0) = X1 ),
% 39.62/5.49      inference(resolution,[status(thm)],[c_11,c_15]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_10,plain,
% 39.62/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | v1_relat_1(X0) ),
% 39.62/5.49      inference(cnf_transformation,[],[f71]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_602,plain,
% 39.62/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ v1_partfun1(X0,X1)
% 39.62/5.49      | k1_relat_1(X0) = X1 ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_598,c_15,c_11,c_10]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_603,plain,
% 39.62/5.49      ( ~ v1_partfun1(X0,X1)
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | k1_relat_1(X0) = X1 ),
% 39.62/5.49      inference(renaming,[status(thm)],[c_602]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1941,plain,
% 39.62/5.49      ( k1_relat_1(X0) = X1
% 39.62/5.49      | v1_partfun1(X0,X1) != iProver_top
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4859,plain,
% 39.62/5.49      ( k1_relat_1(sK6) = sK4 | v1_partfun1(sK6,sK4) != iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_1957,c_1941]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_40,negated_conjecture,
% 39.62/5.49      ( ~ v1_xboole_0(sK2) ),
% 39.62/5.49      inference(cnf_transformation,[],[f90]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_43,plain,
% 39.62/5.49      ( v1_xboole_0(sK2) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_31,negated_conjecture,
% 39.62/5.49      ( v1_funct_1(sK6) ),
% 39.62/5.49      inference(cnf_transformation,[],[f99]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_52,plain,
% 39.62/5.49      ( v1_funct_1(sK6) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_30,negated_conjecture,
% 39.62/5.49      ( v1_funct_2(sK6,sK4,sK2) ),
% 39.62/5.49      inference(cnf_transformation,[],[f100]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_53,plain,
% 39.62/5.49      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_54,plain,
% 39.62/5.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_12,plain,
% 39.62/5.49      ( ~ v1_funct_2(X0,X1,X2)
% 39.62/5.49      | v1_partfun1(X0,X1)
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | v1_xboole_0(X2) ),
% 39.62/5.49      inference(cnf_transformation,[],[f74]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_2131,plain,
% 39.62/5.49      ( ~ v1_funct_2(X0,X1,sK2)
% 39.62/5.49      | v1_partfun1(X0,X1)
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | v1_xboole_0(sK2) ),
% 39.62/5.49      inference(instantiation,[status(thm)],[c_12]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_2316,plain,
% 39.62/5.49      ( ~ v1_funct_2(sK6,X0,sK2)
% 39.62/5.49      | v1_partfun1(sK6,X0)
% 39.62/5.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 39.62/5.49      | ~ v1_funct_1(sK6)
% 39.62/5.49      | v1_xboole_0(sK2) ),
% 39.62/5.49      inference(instantiation,[status(thm)],[c_2131]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_2768,plain,
% 39.62/5.49      ( ~ v1_funct_2(sK6,sK4,sK2)
% 39.62/5.49      | v1_partfun1(sK6,sK4)
% 39.62/5.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 39.62/5.49      | ~ v1_funct_1(sK6)
% 39.62/5.49      | v1_xboole_0(sK2) ),
% 39.62/5.49      inference(instantiation,[status(thm)],[c_2316]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_2769,plain,
% 39.62/5.49      ( v1_funct_2(sK6,sK4,sK2) != iProver_top
% 39.62/5.49      | v1_partfun1(sK6,sK4) = iProver_top
% 39.62/5.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 39.62/5.49      | v1_funct_1(sK6) != iProver_top
% 39.62/5.49      | v1_xboole_0(sK2) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_2768]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_5264,plain,
% 39.62/5.49      ( k1_relat_1(sK6) = sK4 ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_4859,c_43,c_52,c_53,c_54,c_2769]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_5,plain,
% 39.62/5.49      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 39.62/5.49      | ~ v1_relat_1(X1)
% 39.62/5.49      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 39.62/5.49      inference(cnf_transformation,[],[f66]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_9,plain,
% 39.62/5.49      ( ~ r1_subset_1(X0,X1)
% 39.62/5.49      | r1_xboole_0(X0,X1)
% 39.62/5.49      | v1_xboole_0(X0)
% 39.62/5.49      | v1_xboole_0(X1) ),
% 39.62/5.49      inference(cnf_transformation,[],[f69]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_35,negated_conjecture,
% 39.62/5.49      ( r1_subset_1(sK3,sK4) ),
% 39.62/5.49      inference(cnf_transformation,[],[f95]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_540,plain,
% 39.62/5.49      ( r1_xboole_0(X0,X1)
% 39.62/5.49      | v1_xboole_0(X0)
% 39.62/5.49      | v1_xboole_0(X1)
% 39.62/5.49      | sK4 != X1
% 39.62/5.49      | sK3 != X0 ),
% 39.62/5.49      inference(resolution_lifted,[status(thm)],[c_9,c_35]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_541,plain,
% 39.62/5.49      ( r1_xboole_0(sK3,sK4) | v1_xboole_0(sK4) | v1_xboole_0(sK3) ),
% 39.62/5.49      inference(unflattening,[status(thm)],[c_540]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_39,negated_conjecture,
% 39.62/5.49      ( ~ v1_xboole_0(sK3) ),
% 39.62/5.49      inference(cnf_transformation,[],[f91]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_37,negated_conjecture,
% 39.62/5.49      ( ~ v1_xboole_0(sK4) ),
% 39.62/5.49      inference(cnf_transformation,[],[f93]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_543,plain,
% 39.62/5.49      ( r1_xboole_0(sK3,sK4) ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_541,c_39,c_37]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_574,plain,
% 39.62/5.49      ( ~ v1_relat_1(X0)
% 39.62/5.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 39.62/5.49      | k1_relat_1(X0) != sK4
% 39.62/5.49      | sK3 != X1 ),
% 39.62/5.49      inference(resolution_lifted,[status(thm)],[c_5,c_543]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_575,plain,
% 39.62/5.49      ( ~ v1_relat_1(X0)
% 39.62/5.49      | k7_relat_1(X0,sK3) = k1_xboole_0
% 39.62/5.49      | k1_relat_1(X0) != sK4 ),
% 39.62/5.49      inference(unflattening,[status(thm)],[c_574]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1942,plain,
% 39.62/5.49      ( k7_relat_1(X0,sK3) = k1_xboole_0
% 39.62/5.49      | k1_relat_1(X0) != sK4
% 39.62/5.49      | v1_relat_1(X0) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_5269,plain,
% 39.62/5.49      ( k7_relat_1(sK6,sK3) = k1_xboole_0
% 39.62/5.49      | v1_relat_1(sK6) != iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_5264,c_1942]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1967,plain,
% 39.62/5.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.62/5.49      | v1_relat_1(X0) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_3748,plain,
% 39.62/5.49      ( v1_relat_1(sK6) = iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_1957,c_1967]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_7169,plain,
% 39.62/5.49      ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_5269,c_3748]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_7,plain,
% 39.62/5.49      ( ~ v1_relat_1(X0)
% 39.62/5.49      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 39.62/5.49      inference(cnf_transformation,[],[f68]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1968,plain,
% 39.62/5.49      ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
% 39.62/5.49      | v1_relat_1(X0) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_3824,plain,
% 39.62/5.49      ( k1_relat_1(k7_relat_1(sK6,X0)) = k3_xboole_0(k1_relat_1(sK6),X0) ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_3748,c_1968]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_5266,plain,
% 39.62/5.49      ( k1_relat_1(k7_relat_1(sK6,X0)) = k3_xboole_0(sK4,X0) ),
% 39.62/5.49      inference(demodulation,[status(thm)],[c_5264,c_3824]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_7171,plain,
% 39.62/5.49      ( k3_xboole_0(sK4,sK3) = k1_relat_1(k1_xboole_0) ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_7169,c_5266]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_19,plain,
% 39.62/5.49      ( v4_relat_1(sK0(X0),X0) ),
% 39.62/5.49      inference(cnf_transformation,[],[f79]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_21,plain,
% 39.62/5.49      ( ~ v1_partfun1(X0,k1_xboole_0)
% 39.62/5.49      | ~ v4_relat_1(X0,k1_xboole_0)
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | ~ v1_relat_1(X0)
% 39.62/5.49      | k1_xboole_0 = X0 ),
% 39.62/5.49      inference(cnf_transformation,[],[f82]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_684,plain,
% 39.62/5.49      ( ~ v1_partfun1(X0,k1_xboole_0)
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | ~ v1_relat_1(X0)
% 39.62/5.49      | sK0(X1) != X0
% 39.62/5.49      | k1_xboole_0 != X1
% 39.62/5.49      | k1_xboole_0 = X0 ),
% 39.62/5.49      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_685,plain,
% 39.62/5.49      ( ~ v1_partfun1(sK0(k1_xboole_0),k1_xboole_0)
% 39.62/5.49      | ~ v1_funct_1(sK0(k1_xboole_0))
% 39.62/5.49      | ~ v1_relat_1(sK0(k1_xboole_0))
% 39.62/5.49      | k1_xboole_0 = sK0(k1_xboole_0) ),
% 39.62/5.49      inference(unflattening,[status(thm)],[c_684]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_20,plain,
% 39.62/5.49      ( v1_relat_1(sK0(X0)) ),
% 39.62/5.49      inference(cnf_transformation,[],[f78]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_18,plain,
% 39.62/5.49      ( v1_funct_1(sK0(X0)) ),
% 39.62/5.49      inference(cnf_transformation,[],[f80]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_17,plain,
% 39.62/5.49      ( v1_partfun1(sK0(X0),X0) ),
% 39.62/5.49      inference(cnf_transformation,[],[f81]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_695,plain,
% 39.62/5.49      ( k1_xboole_0 = sK0(k1_xboole_0) ),
% 39.62/5.49      inference(forward_subsumption_resolution,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_685,c_20,c_18,c_17]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_635,plain,
% 39.62/5.49      ( ~ v1_partfun1(X0,X1)
% 39.62/5.49      | ~ v1_relat_1(X0)
% 39.62/5.49      | X2 != X1
% 39.62/5.49      | sK0(X2) != X0
% 39.62/5.49      | k1_relat_1(X0) = X1 ),
% 39.62/5.49      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_636,plain,
% 39.62/5.49      ( ~ v1_partfun1(sK0(X0),X0)
% 39.62/5.49      | ~ v1_relat_1(sK0(X0))
% 39.62/5.49      | k1_relat_1(sK0(X0)) = X0 ),
% 39.62/5.49      inference(unflattening,[status(thm)],[c_635]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_640,plain,
% 39.62/5.49      ( k1_relat_1(sK0(X0)) = X0 ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_636,c_20,c_17]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_3444,plain,
% 39.62/5.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_695,c_640]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_7172,plain,
% 39.62/5.49      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 39.62/5.49      inference(light_normalisation,[status(thm)],[c_7171,c_3444]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_32,negated_conjecture,
% 39.62/5.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 39.62/5.49      inference(cnf_transformation,[],[f98]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1954,plain,
% 39.62/5.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4860,plain,
% 39.62/5.49      ( k1_relat_1(sK5) = sK3 | v1_partfun1(sK5,sK3) != iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_1954,c_1941]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_34,negated_conjecture,
% 39.62/5.49      ( v1_funct_1(sK5) ),
% 39.62/5.49      inference(cnf_transformation,[],[f96]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_49,plain,
% 39.62/5.49      ( v1_funct_1(sK5) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_33,negated_conjecture,
% 39.62/5.49      ( v1_funct_2(sK5,sK3,sK2) ),
% 39.62/5.49      inference(cnf_transformation,[],[f97]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_50,plain,
% 39.62/5.49      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_51,plain,
% 39.62/5.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_2321,plain,
% 39.62/5.49      ( ~ v1_funct_2(sK5,X0,sK2)
% 39.62/5.49      | v1_partfun1(sK5,X0)
% 39.62/5.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 39.62/5.49      | ~ v1_funct_1(sK5)
% 39.62/5.49      | v1_xboole_0(sK2) ),
% 39.62/5.49      inference(instantiation,[status(thm)],[c_2131]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_2322,plain,
% 39.62/5.49      ( v1_funct_2(sK5,X0,sK2) != iProver_top
% 39.62/5.49      | v1_partfun1(sK5,X0) = iProver_top
% 39.62/5.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.49      | v1_funct_1(sK5) != iProver_top
% 39.62/5.49      | v1_xboole_0(sK2) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_2321]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_2324,plain,
% 39.62/5.49      ( v1_funct_2(sK5,sK3,sK2) != iProver_top
% 39.62/5.49      | v1_partfun1(sK5,sK3) = iProver_top
% 39.62/5.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 39.62/5.49      | v1_funct_1(sK5) != iProver_top
% 39.62/5.49      | v1_xboole_0(sK2) = iProver_top ),
% 39.62/5.49      inference(instantiation,[status(thm)],[c_2322]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_5276,plain,
% 39.62/5.49      ( k1_relat_1(sK5) = sK3 ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_4860,c_43,c_49,c_50,c_51,c_2324]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_0,plain,
% 39.62/5.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 39.62/5.49      inference(cnf_transformation,[],[f62]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_312,plain,
% 39.62/5.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 39.62/5.49      inference(prop_impl,[status(thm)],[c_0]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_554,plain,
% 39.62/5.49      ( ~ v1_relat_1(X0)
% 39.62/5.49      | X1 != X2
% 39.62/5.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 39.62/5.49      | k3_xboole_0(X2,X3) != k1_xboole_0
% 39.62/5.49      | k1_relat_1(X0) != X3 ),
% 39.62/5.49      inference(resolution_lifted,[status(thm)],[c_312,c_5]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_555,plain,
% 39.62/5.49      ( ~ v1_relat_1(X0)
% 39.62/5.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 39.62/5.49      | k3_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0 ),
% 39.62/5.49      inference(unflattening,[status(thm)],[c_554]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1943,plain,
% 39.62/5.49      ( k7_relat_1(X0,X1) = k1_xboole_0
% 39.62/5.49      | k3_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0
% 39.62/5.49      | v1_relat_1(X0) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_34616,plain,
% 39.62/5.49      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 39.62/5.49      | k3_xboole_0(X0,sK3) != k1_xboole_0
% 39.62/5.49      | v1_relat_1(sK5) != iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_5276,c_1943]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_3749,plain,
% 39.62/5.49      ( v1_relat_1(sK5) = iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_1954,c_1967]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_34876,plain,
% 39.62/5.49      ( k3_xboole_0(X0,sK3) != k1_xboole_0
% 39.62/5.49      | k7_relat_1(sK5,X0) = k1_xboole_0 ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_34616,c_3749]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_34877,plain,
% 39.62/5.49      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 39.62/5.49      | k3_xboole_0(X0,sK3) != k1_xboole_0 ),
% 39.62/5.49      inference(renaming,[status(thm)],[c_34876]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_34879,plain,
% 39.62/5.49      ( k7_relat_1(sK5,sK4) = k1_xboole_0 ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_7172,c_34877]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1,plain,
% 39.62/5.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 39.62/5.49      inference(cnf_transformation,[],[f61]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_314,plain,
% 39.62/5.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 39.62/5.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_569,plain,
% 39.62/5.49      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK4 != X1 | sK3 != X0 ),
% 39.62/5.49      inference(resolution_lifted,[status(thm)],[c_314,c_543]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_570,plain,
% 39.62/5.49      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 39.62/5.49      inference(unflattening,[status(thm)],[c_569]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_6,plain,
% 39.62/5.49      ( ~ v1_relat_1(X0)
% 39.62/5.49      | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
% 39.62/5.49      inference(cnf_transformation,[],[f67]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1969,plain,
% 39.62/5.49      ( k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1)
% 39.62/5.49      | v1_relat_1(X0) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4024,plain,
% 39.62/5.49      ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0)) = k7_relat_1(sK5,X0) ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_3749,c_1969]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_3827,plain,
% 39.62/5.49      ( k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(k1_relat_1(sK5),X0) ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_3749,c_1968]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4025,plain,
% 39.62/5.49      ( k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0))) = k7_relat_1(sK5,X0) ),
% 39.62/5.49      inference(light_normalisation,[status(thm)],[c_4024,c_3827]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_5278,plain,
% 39.62/5.49      ( k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(sK3,X0) ),
% 39.62/5.49      inference(demodulation,[status(thm)],[c_5276,c_3827]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_8262,plain,
% 39.62/5.49      ( k7_relat_1(sK5,k3_xboole_0(sK3,X0)) = k7_relat_1(sK5,X0) ),
% 39.62/5.49      inference(light_normalisation,[status(thm)],[c_4025,c_4025,c_5278]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_8264,plain,
% 39.62/5.49      ( k7_relat_1(sK5,sK4) = k7_relat_1(sK5,k1_xboole_0) ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_570,c_8262]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_76072,plain,
% 39.62/5.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 39.62/5.49      inference(demodulation,[status(thm)],[c_34879,c_8264]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_16,plain,
% 39.62/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 39.62/5.49      inference(cnf_transformation,[],[f77]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1965,plain,
% 39.62/5.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 39.62/5.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.62/5.49      | v1_funct_1(X2) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4152,plain,
% 39.62/5.49      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 39.62/5.49      | v1_funct_1(sK5) != iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_1954,c_1965]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4854,plain,
% 39.62/5.49      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_4152,c_49]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_36,negated_conjecture,
% 39.62/5.49      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 39.62/5.49      inference(cnf_transformation,[],[f94]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1951,plain,
% 39.62/5.49      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_2,plain,
% 39.62/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.62/5.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 39.62/5.49      inference(cnf_transformation,[],[f63]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1972,plain,
% 39.62/5.49      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 39.62/5.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4058,plain,
% 39.62/5.49      ( k9_subset_1(sK1,X0,sK4) = k3_xboole_0(X0,sK4) ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_1951,c_1972]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4151,plain,
% 39.62/5.49      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 39.62/5.49      | v1_funct_1(sK6) != iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_1957,c_1965]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4790,plain,
% 39.62/5.49      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_4151,c_52]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_24,plain,
% 39.62/5.49      ( ~ v1_funct_2(X0,X1,X2)
% 39.62/5.49      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 39.62/5.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | ~ v1_funct_1(X3)
% 39.62/5.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 39.62/5.49      | v1_xboole_0(X5)
% 39.62/5.49      | v1_xboole_0(X2)
% 39.62/5.49      | v1_xboole_0(X4)
% 39.62/5.49      | v1_xboole_0(X1)
% 39.62/5.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 39.62/5.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 39.62/5.49      inference(cnf_transformation,[],[f107]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_27,plain,
% 39.62/5.49      ( ~ v1_funct_2(X0,X1,X2)
% 39.62/5.49      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | ~ v1_funct_1(X3)
% 39.62/5.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 39.62/5.49      | v1_xboole_0(X5)
% 39.62/5.49      | v1_xboole_0(X2)
% 39.62/5.49      | v1_xboole_0(X4)
% 39.62/5.49      | v1_xboole_0(X1) ),
% 39.62/5.49      inference(cnf_transformation,[],[f86]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_26,plain,
% 39.62/5.49      ( ~ v1_funct_2(X0,X1,X2)
% 39.62/5.49      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 39.62/5.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | ~ v1_funct_1(X3)
% 39.62/5.49      | v1_xboole_0(X5)
% 39.62/5.49      | v1_xboole_0(X2)
% 39.62/5.49      | v1_xboole_0(X4)
% 39.62/5.49      | v1_xboole_0(X1) ),
% 39.62/5.49      inference(cnf_transformation,[],[f87]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_25,plain,
% 39.62/5.49      ( ~ v1_funct_2(X0,X1,X2)
% 39.62/5.49      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | ~ v1_funct_1(X3)
% 39.62/5.49      | v1_xboole_0(X5)
% 39.62/5.49      | v1_xboole_0(X2)
% 39.62/5.49      | v1_xboole_0(X4)
% 39.62/5.49      | v1_xboole_0(X1) ),
% 39.62/5.49      inference(cnf_transformation,[],[f88]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_232,plain,
% 39.62/5.49      ( ~ v1_funct_1(X3)
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.49      | ~ v1_funct_2(X0,X1,X2)
% 39.62/5.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.49      | v1_xboole_0(X5)
% 39.62/5.49      | v1_xboole_0(X2)
% 39.62/5.49      | v1_xboole_0(X4)
% 39.62/5.49      | v1_xboole_0(X1)
% 39.62/5.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 39.62/5.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_24,c_27,c_26,c_25]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_233,plain,
% 39.62/5.49      ( ~ v1_funct_2(X0,X1,X2)
% 39.62/5.49      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.49      | ~ v1_funct_1(X0)
% 39.62/5.49      | ~ v1_funct_1(X3)
% 39.62/5.49      | v1_xboole_0(X1)
% 39.62/5.49      | v1_xboole_0(X2)
% 39.62/5.49      | v1_xboole_0(X4)
% 39.62/5.49      | v1_xboole_0(X5)
% 39.62/5.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 39.62/5.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 39.62/5.49      inference(renaming,[status(thm)],[c_232]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_1945,plain,
% 39.62/5.49      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 39.62/5.49      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 39.62/5.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.62/5.49      | v1_funct_2(X5,X4,X1) != iProver_top
% 39.62/5.49      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 39.62/5.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.62/5.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 39.62/5.49      | v1_funct_1(X2) != iProver_top
% 39.62/5.49      | v1_funct_1(X5) != iProver_top
% 39.62/5.49      | v1_xboole_0(X3) = iProver_top
% 39.62/5.49      | v1_xboole_0(X1) = iProver_top
% 39.62/5.49      | v1_xboole_0(X4) = iProver_top
% 39.62/5.49      | v1_xboole_0(X0) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_7658,plain,
% 39.62/5.49      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 39.62/5.49      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 39.62/5.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.49      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 39.62/5.49      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.49      | v1_funct_1(X1) != iProver_top
% 39.62/5.49      | v1_funct_1(sK6) != iProver_top
% 39.62/5.49      | v1_xboole_0(X0) = iProver_top
% 39.62/5.49      | v1_xboole_0(X2) = iProver_top
% 39.62/5.49      | v1_xboole_0(sK2) = iProver_top
% 39.62/5.49      | v1_xboole_0(sK4) = iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_4790,c_1945]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_46,plain,
% 39.62/5.49      ( v1_xboole_0(sK4) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_15655,plain,
% 39.62/5.49      ( v1_funct_1(X1) != iProver_top
% 39.62/5.49      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.49      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 39.62/5.49      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.49      | v1_xboole_0(X0) = iProver_top
% 39.62/5.49      | v1_xboole_0(X2) = iProver_top ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_7658,c_43,c_46,c_52,c_53,c_54]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_15656,plain,
% 39.62/5.49      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 39.62/5.49      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 39.62/5.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.49      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.49      | v1_funct_1(X1) != iProver_top
% 39.62/5.49      | v1_xboole_0(X2) = iProver_top
% 39.62/5.49      | v1_xboole_0(X0) = iProver_top ),
% 39.62/5.49      inference(renaming,[status(thm)],[c_15655]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_15668,plain,
% 39.62/5.49      ( k2_partfun1(X0,sK2,X1,k3_xboole_0(X0,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,X0,sK4))
% 39.62/5.49      | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),X0) = X1
% 39.62/5.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.49      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.49      | v1_funct_1(X1) != iProver_top
% 39.62/5.49      | v1_xboole_0(X0) = iProver_top
% 39.62/5.49      | v1_xboole_0(sK1) = iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_4058,c_15656]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_15669,plain,
% 39.62/5.49      ( k2_partfun1(X0,sK2,X1,k3_xboole_0(X0,sK4)) != k7_relat_1(sK6,k3_xboole_0(X0,sK4))
% 39.62/5.49      | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),X0) = X1
% 39.62/5.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.49      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.49      | v1_funct_1(X1) != iProver_top
% 39.62/5.49      | v1_xboole_0(X0) = iProver_top
% 39.62/5.49      | v1_xboole_0(sK1) = iProver_top ),
% 39.62/5.49      inference(light_normalisation,[status(thm)],[c_15668,c_4058]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_41,negated_conjecture,
% 39.62/5.49      ( ~ v1_xboole_0(sK1) ),
% 39.62/5.49      inference(cnf_transformation,[],[f89]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_42,plain,
% 39.62/5.49      ( v1_xboole_0(sK1) != iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_47,plain,
% 39.62/5.49      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.62/5.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_18397,plain,
% 39.62/5.49      ( v1_xboole_0(X0) = iProver_top
% 39.62/5.49      | v1_funct_1(X1) != iProver_top
% 39.62/5.49      | k2_partfun1(X0,sK2,X1,k3_xboole_0(X0,sK4)) != k7_relat_1(sK6,k3_xboole_0(X0,sK4))
% 39.62/5.49      | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),X0) = X1
% 39.62/5.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.49      inference(global_propositional_subsumption,
% 39.62/5.49                [status(thm)],
% 39.62/5.49                [c_15669,c_42,c_47]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_18398,plain,
% 39.62/5.49      ( k2_partfun1(X0,sK2,X1,k3_xboole_0(X0,sK4)) != k7_relat_1(sK6,k3_xboole_0(X0,sK4))
% 39.62/5.49      | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),X0) = X1
% 39.62/5.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.49      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.49      | v1_funct_1(X1) != iProver_top
% 39.62/5.49      | v1_xboole_0(X0) = iProver_top ),
% 39.62/5.49      inference(renaming,[status(thm)],[c_18397]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_18405,plain,
% 39.62/5.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.49      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 39.62/5.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 39.62/5.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 39.62/5.49      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.49      | v1_funct_1(sK5) != iProver_top
% 39.62/5.49      | v1_xboole_0(sK3) = iProver_top ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_4854,c_18398]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4023,plain,
% 39.62/5.49      ( k7_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),X0)) = k7_relat_1(sK6,X0) ),
% 39.62/5.49      inference(superposition,[status(thm)],[c_3748,c_1969]) ).
% 39.62/5.49  
% 39.62/5.49  cnf(c_4026,plain,
% 39.62/5.50      ( k7_relat_1(sK6,k1_relat_1(k7_relat_1(sK6,X0))) = k7_relat_1(sK6,X0) ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_4023,c_3824]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_8640,plain,
% 39.62/5.50      ( k7_relat_1(sK6,k3_xboole_0(sK4,X0)) = k7_relat_1(sK6,X0) ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_4026,c_4026,c_5266]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_13654,plain,
% 39.62/5.50      ( k7_relat_1(sK6,k1_xboole_0) = k7_relat_1(sK6,sK3) ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_7172,c_8640]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_13655,plain,
% 39.62/5.50      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_13654,c_7169]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18422,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 39.62/5.50      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | v1_funct_1(sK5) != iProver_top
% 39.62/5.50      | v1_xboole_0(sK3) = iProver_top ),
% 39.62/5.50      inference(light_normalisation,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_18405,c_570,c_13655]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_1958,plain,
% 39.62/5.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 39.62/5.50      | v1_funct_2(X3,X4,X2) != iProver_top
% 39.62/5.50      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 39.62/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.62/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 39.62/5.50      | v1_funct_1(X0) != iProver_top
% 39.62/5.50      | v1_funct_1(X3) != iProver_top
% 39.62/5.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 39.62/5.50      | v1_xboole_0(X5) = iProver_top
% 39.62/5.50      | v1_xboole_0(X2) = iProver_top
% 39.62/5.50      | v1_xboole_0(X4) = iProver_top
% 39.62/5.50      | v1_xboole_0(X1) = iProver_top ),
% 39.62/5.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_1960,plain,
% 39.62/5.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 39.62/5.50      | v1_funct_2(X3,X4,X2) != iProver_top
% 39.62/5.50      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 39.62/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.62/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 39.62/5.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
% 39.62/5.50      | v1_funct_1(X0) != iProver_top
% 39.62/5.50      | v1_funct_1(X3) != iProver_top
% 39.62/5.50      | v1_xboole_0(X5) = iProver_top
% 39.62/5.50      | v1_xboole_0(X2) = iProver_top
% 39.62/5.50      | v1_xboole_0(X4) = iProver_top
% 39.62/5.50      | v1_xboole_0(X1) = iProver_top ),
% 39.62/5.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_5085,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 39.62/5.50      | v1_funct_2(X5,X2,X3) != iProver_top
% 39.62/5.50      | v1_funct_2(X4,X1,X3) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 39.62/5.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 39.62/5.50      | v1_funct_1(X5) != iProver_top
% 39.62/5.50      | v1_funct_1(X4) != iProver_top
% 39.62/5.50      | v1_funct_1(k1_tmap_1(X0,X3,X1,X2,X4,X5)) != iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top
% 39.62/5.50      | v1_xboole_0(X3) = iProver_top
% 39.62/5.50      | v1_xboole_0(X1) = iProver_top
% 39.62/5.50      | v1_xboole_0(X2) = iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_1960,c_1965]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_9410,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 39.62/5.50      | v1_funct_2(X5,X2,X3) != iProver_top
% 39.62/5.50      | v1_funct_2(X4,X1,X3) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 39.62/5.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 39.62/5.50      | v1_funct_1(X5) != iProver_top
% 39.62/5.50      | v1_funct_1(X4) != iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top
% 39.62/5.50      | v1_xboole_0(X3) = iProver_top
% 39.62/5.50      | v1_xboole_0(X1) = iProver_top
% 39.62/5.50      | v1_xboole_0(X2) = iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_1958,c_5085]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_12361,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 39.62/5.50      | v1_funct_2(X2,X1,sK2) != iProver_top
% 39.62/5.50      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | v1_funct_1(X2) != iProver_top
% 39.62/5.50      | v1_funct_1(sK6) != iProver_top
% 39.62/5.50      | v1_xboole_0(X1) = iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top
% 39.62/5.50      | v1_xboole_0(sK2) = iProver_top
% 39.62/5.50      | v1_xboole_0(sK4) = iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_1957,c_9410]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_4,plain,
% 39.62/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.62/5.50      | ~ v1_xboole_0(X1)
% 39.62/5.50      | v1_xboole_0(X0) ),
% 39.62/5.50      inference(cnf_transformation,[],[f65]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_2023,plain,
% 39.62/5.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 39.62/5.50      | ~ v1_xboole_0(X0)
% 39.62/5.50      | v1_xboole_0(sK4) ),
% 39.62/5.50      inference(instantiation,[status(thm)],[c_4]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_2024,plain,
% 39.62/5.50      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | v1_xboole_0(X0) != iProver_top
% 39.62/5.50      | v1_xboole_0(sK4) = iProver_top ),
% 39.62/5.50      inference(predicate_to_equality,[status(thm)],[c_2023]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_13721,plain,
% 39.62/5.50      ( v1_xboole_0(X1) = iProver_top
% 39.62/5.50      | v1_funct_2(X2,X1,sK2) != iProver_top
% 39.62/5.50      | k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | v1_funct_1(X2) != iProver_top ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_12361,c_43,c_46,c_52,c_53,c_2024]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_13722,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 39.62/5.50      | v1_funct_2(X2,X1,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | v1_funct_1(X2) != iProver_top
% 39.62/5.50      | v1_xboole_0(X1) = iProver_top ),
% 39.62/5.50      inference(renaming,[status(thm)],[c_13721]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_13730,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
% 39.62/5.50      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | v1_funct_1(sK5) != iProver_top
% 39.62/5.50      | v1_xboole_0(sK3) = iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_1954,c_13722]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_44,plain,
% 39.62/5.50      ( v1_xboole_0(sK3) != iProver_top ),
% 39.62/5.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_14205,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_13730,c_44,c_49,c_50]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_14211,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0)
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_1951,c_14205]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_38,negated_conjecture,
% 39.62/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 39.62/5.50      inference(cnf_transformation,[],[f92]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_45,plain,
% 39.62/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.62/5.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_14216,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_14211,c_45]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18423,plain,
% 39.62/5.50      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 39.62/5.50      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | v1_funct_1(sK5) != iProver_top
% 39.62/5.50      | v1_xboole_0(sK3) = iProver_top ),
% 39.62/5.50      inference(demodulation,[status(thm)],[c_18422,c_14216]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_28,negated_conjecture,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 39.62/5.50      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 39.62/5.50      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 39.62/5.50      inference(cnf_transformation,[],[f102]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_4162,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 39.62/5.50      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 39.62/5.50      | k2_partfun1(sK4,sK2,sK6,k3_xboole_0(sK3,sK4)) != k2_partfun1(sK3,sK2,sK5,k3_xboole_0(sK3,sK4)) ),
% 39.62/5.50      inference(demodulation,[status(thm)],[c_4058,c_28]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_4163,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 39.62/5.50      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 39.62/5.50      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_4162,c_570]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_5327,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 39.62/5.50      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 39.62/5.50      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 39.62/5.50      inference(demodulation,[status(thm)],[c_4163,c_4790,c_4854]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_14220,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 39.62/5.50      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 39.62/5.50      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 39.62/5.50      inference(demodulation,[status(thm)],[c_14216,c_5327]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_14221,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 39.62/5.50      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 39.62/5.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_14220,c_13655]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_14222,plain,
% 39.62/5.50      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 39.62/5.50      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 39.62/5.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 39.62/5.50      inference(demodulation,[status(thm)],[c_14221,c_14216]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_23,plain,
% 39.62/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.62/5.50      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 39.62/5.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 39.62/5.50      | ~ v1_funct_1(X0)
% 39.62/5.50      | ~ v1_funct_1(X3)
% 39.62/5.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 39.62/5.50      | v1_xboole_0(X5)
% 39.62/5.50      | v1_xboole_0(X2)
% 39.62/5.50      | v1_xboole_0(X4)
% 39.62/5.50      | v1_xboole_0(X1)
% 39.62/5.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 39.62/5.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 39.62/5.50      inference(cnf_transformation,[],[f106]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_239,plain,
% 39.62/5.50      ( ~ v1_funct_1(X3)
% 39.62/5.50      | ~ v1_funct_1(X0)
% 39.62/5.50      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.50      | ~ v1_funct_2(X0,X1,X2)
% 39.62/5.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.50      | v1_xboole_0(X5)
% 39.62/5.50      | v1_xboole_0(X2)
% 39.62/5.50      | v1_xboole_0(X4)
% 39.62/5.50      | v1_xboole_0(X1)
% 39.62/5.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 39.62/5.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_23,c_27,c_26,c_25]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_240,plain,
% 39.62/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.62/5.50      | ~ v1_funct_2(X3,X4,X2)
% 39.62/5.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 39.62/5.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 39.62/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.62/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.62/5.50      | ~ v1_funct_1(X0)
% 39.62/5.50      | ~ v1_funct_1(X3)
% 39.62/5.50      | v1_xboole_0(X1)
% 39.62/5.50      | v1_xboole_0(X2)
% 39.62/5.50      | v1_xboole_0(X4)
% 39.62/5.50      | v1_xboole_0(X5)
% 39.62/5.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 39.62/5.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 39.62/5.50      inference(renaming,[status(thm)],[c_239]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_1944,plain,
% 39.62/5.50      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 39.62/5.50      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 39.62/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.62/5.50      | v1_funct_2(X5,X4,X1) != iProver_top
% 39.62/5.50      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 39.62/5.50      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 39.62/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.62/5.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 39.62/5.50      | v1_funct_1(X2) != iProver_top
% 39.62/5.50      | v1_funct_1(X5) != iProver_top
% 39.62/5.50      | v1_xboole_0(X3) = iProver_top
% 39.62/5.50      | v1_xboole_0(X1) = iProver_top
% 39.62/5.50      | v1_xboole_0(X4) = iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top ),
% 39.62/5.50      inference(predicate_to_equality,[status(thm)],[c_240]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7205,plain,
% 39.62/5.50      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 39.62/5.50      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 39.62/5.50      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.50      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.50      | v1_funct_1(X1) != iProver_top
% 39.62/5.50      | v1_funct_1(sK6) != iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top
% 39.62/5.50      | v1_xboole_0(X2) = iProver_top
% 39.62/5.50      | v1_xboole_0(sK2) = iProver_top
% 39.62/5.50      | v1_xboole_0(sK4) = iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_4790,c_1944]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7471,plain,
% 39.62/5.50      ( v1_funct_1(X1) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.50      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.50      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 39.62/5.50      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 39.62/5.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top
% 39.62/5.50      | v1_xboole_0(X2) = iProver_top ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_7205,c_43,c_46,c_52,c_53,c_54]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7472,plain,
% 39.62/5.50      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 39.62/5.50      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 39.62/5.50      | v1_funct_2(X1,X0,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 39.62/5.50      | v1_funct_1(X1) != iProver_top
% 39.62/5.50      | v1_xboole_0(X2) = iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top ),
% 39.62/5.50      inference(renaming,[status(thm)],[c_7471]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7478,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 39.62/5.50      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | v1_funct_1(sK5) != iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top
% 39.62/5.50      | v1_xboole_0(sK3) = iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_4854,c_7472]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_2065,plain,
% 39.62/5.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 39.62/5.50      | ~ v1_xboole_0(X0)
% 39.62/5.50      | v1_xboole_0(sK3) ),
% 39.62/5.50      inference(instantiation,[status(thm)],[c_4]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_2066,plain,
% 39.62/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | v1_xboole_0(X0) != iProver_top
% 39.62/5.50      | v1_xboole_0(sK3) = iProver_top ),
% 39.62/5.50      inference(predicate_to_equality,[status(thm)],[c_2065]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7560,plain,
% 39.62/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 39.62/5.50      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6 ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_7478,c_44,c_49,c_50,c_51,c_2066]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7561,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 39.62/5.50      inference(renaming,[status(thm)],[c_7560]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7566,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_4058,c_7561]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7567,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_7566,c_570]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7568,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(demodulation,[status(thm)],[c_7567,c_4058]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7569,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_7568,c_570]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7570,plain,
% 39.62/5.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 39.62/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 39.62/5.50      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 39.62/5.50      inference(predicate_to_equality_rev,[status(thm)],[c_7569]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_7655,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_7569,c_38,c_36,c_7570]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_14219,plain,
% 39.62/5.50      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 39.62/5.50      inference(demodulation,[status(thm)],[c_14216,c_7655]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_14223,plain,
% 39.62/5.50      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 39.62/5.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_14219,c_13655]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_15192,plain,
% 39.62/5.50      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 39.62/5.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_14222,c_14223]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_15663,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 39.62/5.50      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 39.62/5.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | v1_funct_1(sK5) != iProver_top
% 39.62/5.50      | v1_xboole_0(X0) = iProver_top
% 39.62/5.50      | v1_xboole_0(sK3) = iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_4854,c_15656]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18120,plain,
% 39.62/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 39.62/5.50      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5 ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_15663,c_44,c_49,c_50,c_51,c_2066]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18121,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 39.62/5.50      inference(renaming,[status(thm)],[c_18120]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18126,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(superposition,[status(thm)],[c_4058,c_18121]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18127,plain,
% 39.62/5.50      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(light_normalisation,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_18126,c_570,c_13655]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18128,plain,
% 39.62/5.50      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK5,sK4) != k1_xboole_0
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(demodulation,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_18127,c_4058,c_8262,c_14216]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18129,plain,
% 39.62/5.50      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 39.62/5.50      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 39.62/5.50      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.62/5.50      inference(light_normalisation,[status(thm)],[c_18128,c_8264]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18130,plain,
% 39.62/5.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 39.62/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 39.62/5.50      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 39.62/5.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 39.62/5.50      inference(predicate_to_equality_rev,[status(thm)],[c_18129]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(c_18448,plain,
% 39.62/5.50      ( k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 39.62/5.50      inference(global_propositional_subsumption,
% 39.62/5.50                [status(thm)],
% 39.62/5.50                [c_18423,c_38,c_36,c_15192,c_18130]) ).
% 39.62/5.50  
% 39.62/5.50  cnf(contradiction,plain,
% 39.62/5.50      ( $false ),
% 39.62/5.50      inference(minisat,[status(thm)],[c_76072,c_18448]) ).
% 39.62/5.50  
% 39.62/5.50  
% 39.62/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.62/5.50  
% 39.62/5.50  ------                               Statistics
% 39.62/5.50  
% 39.62/5.50  ------ General
% 39.62/5.50  
% 39.62/5.50  abstr_ref_over_cycles:                  0
% 39.62/5.50  abstr_ref_under_cycles:                 0
% 39.62/5.50  gc_basic_clause_elim:                   0
% 39.62/5.50  forced_gc_time:                         0
% 39.62/5.50  parsing_time:                           0.027
% 39.62/5.50  unif_index_cands_time:                  0.
% 39.62/5.50  unif_index_add_time:                    0.
% 39.62/5.50  orderings_time:                         0.
% 39.62/5.50  out_proof_time:                         0.031
% 39.62/5.50  total_time:                             4.701
% 39.62/5.50  num_of_symbols:                         57
% 39.62/5.50  num_of_terms:                           172143
% 39.62/5.50  
% 39.62/5.50  ------ Preprocessing
% 39.62/5.50  
% 39.62/5.50  num_of_splits:                          0
% 39.62/5.50  num_of_split_atoms:                     0
% 39.62/5.50  num_of_reused_defs:                     0
% 39.62/5.50  num_eq_ax_congr_red:                    6
% 39.62/5.50  num_of_sem_filtered_clauses:            1
% 39.62/5.50  num_of_subtypes:                        0
% 39.62/5.50  monotx_restored_types:                  0
% 39.62/5.50  sat_num_of_epr_types:                   0
% 39.62/5.50  sat_num_of_non_cyclic_types:            0
% 39.62/5.50  sat_guarded_non_collapsed_types:        0
% 39.62/5.50  num_pure_diseq_elim:                    0
% 39.62/5.50  simp_replaced_by:                       0
% 39.62/5.50  res_preprocessed:                       195
% 39.62/5.50  prep_upred:                             0
% 39.62/5.50  prep_unflattend:                        48
% 39.62/5.50  smt_new_axioms:                         0
% 39.62/5.50  pred_elim_cands:                        6
% 39.62/5.50  pred_elim:                              3
% 39.62/5.50  pred_elim_cl:                           2
% 39.62/5.50  pred_elim_cycles:                       7
% 39.62/5.50  merged_defs:                            2
% 39.62/5.50  merged_defs_ncl:                        0
% 39.62/5.50  bin_hyper_res:                          2
% 39.62/5.50  prep_cycles:                            4
% 39.62/5.50  pred_elim_time:                         0.013
% 39.62/5.50  splitting_time:                         0.
% 39.62/5.50  sem_filter_time:                        0.
% 39.62/5.50  monotx_time:                            0.001
% 39.62/5.50  subtype_inf_time:                       0.
% 39.62/5.50  
% 39.62/5.50  ------ Problem properties
% 39.62/5.50  
% 39.62/5.50  clauses:                                39
% 39.62/5.50  conjectures:                            13
% 39.62/5.50  epr:                                    8
% 39.62/5.50  horn:                                   32
% 39.62/5.50  ground:                                 15
% 39.62/5.50  unary:                                  20
% 39.62/5.50  binary:                                 5
% 39.62/5.50  lits:                                   141
% 39.62/5.50  lits_eq:                                22
% 39.62/5.50  fd_pure:                                0
% 39.62/5.50  fd_pseudo:                              0
% 39.62/5.50  fd_cond:                                1
% 39.62/5.50  fd_pseudo_cond:                         1
% 39.62/5.50  ac_symbols:                             0
% 39.62/5.50  
% 39.62/5.50  ------ Propositional Solver
% 39.62/5.50  
% 39.62/5.50  prop_solver_calls:                      45
% 39.62/5.50  prop_fast_solver_calls:                 17544
% 39.62/5.50  smt_solver_calls:                       0
% 39.62/5.50  smt_fast_solver_calls:                  0
% 39.62/5.50  prop_num_of_clauses:                    33819
% 39.62/5.50  prop_preprocess_simplified:             64865
% 39.62/5.50  prop_fo_subsumed:                       1759
% 39.62/5.50  prop_solver_time:                       0.
% 39.62/5.50  smt_solver_time:                        0.
% 39.62/5.50  smt_fast_solver_time:                   0.
% 39.62/5.50  prop_fast_solver_time:                  0.
% 39.62/5.50  prop_unsat_core_time:                   0.004
% 39.62/5.50  
% 39.62/5.50  ------ QBF
% 39.62/5.50  
% 39.62/5.50  qbf_q_res:                              0
% 39.62/5.50  qbf_num_tautologies:                    0
% 39.62/5.50  qbf_prep_cycles:                        0
% 39.62/5.50  
% 39.62/5.50  ------ BMC1
% 39.62/5.50  
% 39.62/5.50  bmc1_current_bound:                     -1
% 39.62/5.50  bmc1_last_solved_bound:                 -1
% 39.62/5.50  bmc1_unsat_core_size:                   -1
% 39.62/5.50  bmc1_unsat_core_parents_size:           -1
% 39.62/5.50  bmc1_merge_next_fun:                    0
% 39.62/5.50  bmc1_unsat_core_clauses_time:           0.
% 39.62/5.50  
% 39.62/5.50  ------ Instantiation
% 39.62/5.50  
% 39.62/5.50  inst_num_of_clauses:                    4573
% 39.62/5.50  inst_num_in_passive:                    623
% 39.62/5.50  inst_num_in_active:                     4302
% 39.62/5.50  inst_num_in_unprocessed:                2156
% 39.62/5.50  inst_num_of_loops:                      4899
% 39.62/5.50  inst_num_of_learning_restarts:          1
% 39.62/5.50  inst_num_moves_active_passive:          592
% 39.62/5.50  inst_lit_activity:                      0
% 39.62/5.50  inst_lit_activity_moves:                4
% 39.62/5.50  inst_num_tautologies:                   0
% 39.62/5.50  inst_num_prop_implied:                  0
% 39.62/5.50  inst_num_existing_simplified:           0
% 39.62/5.50  inst_num_eq_res_simplified:             0
% 39.62/5.50  inst_num_child_elim:                    0
% 39.62/5.50  inst_num_of_dismatching_blockings:      5675
% 39.62/5.50  inst_num_of_non_proper_insts:           6911
% 39.62/5.50  inst_num_of_duplicates:                 0
% 39.62/5.50  inst_inst_num_from_inst_to_res:         0
% 39.62/5.50  inst_dismatching_checking_time:         0.
% 39.62/5.50  
% 39.62/5.50  ------ Resolution
% 39.62/5.50  
% 39.62/5.50  res_num_of_clauses:                     57
% 39.62/5.50  res_num_in_passive:                     57
% 39.62/5.50  res_num_in_active:                      0
% 39.62/5.50  res_num_of_loops:                       199
% 39.62/5.50  res_forward_subset_subsumed:            1016
% 39.62/5.50  res_backward_subset_subsumed:           0
% 39.62/5.50  res_forward_subsumed:                   0
% 39.62/5.50  res_backward_subsumed:                  0
% 39.62/5.50  res_forward_subsumption_resolution:     5
% 39.62/5.50  res_backward_subsumption_resolution:    0
% 39.62/5.50  res_clause_to_clause_subsumption:       5568
% 39.62/5.50  res_orphan_elimination:                 0
% 39.62/5.50  res_tautology_del:                      255
% 39.62/5.50  res_num_eq_res_simplified:              0
% 39.62/5.50  res_num_sel_changes:                    0
% 39.62/5.50  res_moves_from_active_to_pass:          0
% 39.62/5.50  
% 39.62/5.50  ------ Superposition
% 39.62/5.50  
% 39.62/5.50  sup_time_total:                         0.
% 39.62/5.50  sup_time_generating:                    0.
% 39.62/5.50  sup_time_sim_full:                      0.
% 39.62/5.50  sup_time_sim_immed:                     0.
% 39.62/5.50  
% 39.62/5.50  sup_num_of_clauses:                     1300
% 39.62/5.50  sup_num_in_active:                      851
% 39.62/5.50  sup_num_in_passive:                     449
% 39.62/5.50  sup_num_of_loops:                       978
% 39.62/5.50  sup_fw_superposition:                   1748
% 39.62/5.50  sup_bw_superposition:                   250
% 39.62/5.50  sup_immediate_simplified:               1266
% 39.62/5.50  sup_given_eliminated:                   0
% 39.62/5.50  comparisons_done:                       0
% 39.62/5.50  comparisons_avoided:                    0
% 39.62/5.50  
% 39.62/5.50  ------ Simplifications
% 39.62/5.50  
% 39.62/5.50  
% 39.62/5.50  sim_fw_subset_subsumed:                 24
% 39.62/5.50  sim_bw_subset_subsumed:                 9
% 39.62/5.50  sim_fw_subsumed:                        524
% 39.62/5.50  sim_bw_subsumed:                        55
% 39.62/5.50  sim_fw_subsumption_res:                 0
% 39.62/5.50  sim_bw_subsumption_res:                 0
% 39.62/5.50  sim_tautology_del:                      0
% 39.62/5.50  sim_eq_tautology_del:                   21
% 39.62/5.50  sim_eq_res_simp:                        0
% 39.62/5.50  sim_fw_demodulated:                     976
% 39.62/5.50  sim_bw_demodulated:                     82
% 39.62/5.50  sim_light_normalised:                   475
% 39.62/5.50  sim_joinable_taut:                      0
% 39.62/5.50  sim_joinable_simp:                      0
% 39.62/5.50  sim_ac_normalised:                      0
% 39.62/5.50  sim_smt_subsumption:                    0
% 39.62/5.50  
%------------------------------------------------------------------------------
