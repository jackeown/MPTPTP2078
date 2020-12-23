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
% DateTime   : Thu Dec  3 12:21:36 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  214 (1623 expanded)
%              Number of clauses        :  132 ( 385 expanded)
%              Number of leaves         :   21 ( 629 expanded)
%              Depth                    :   23
%              Number of atoms          : 1192 (20286 expanded)
%              Number of equality atoms :  529 (4893 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f68,plain,(
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

fof(f67,plain,(
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

fof(f66,plain,(
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

fof(f65,plain,
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

fof(f71,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f52,f70,f69,f68,f67,f66,f65])).

fof(f118,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f71])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f71])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f116,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f71])).

fof(f109,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f71])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f78,f80])).

fof(f21,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f128,plain,(
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
    inference(equality_resolution,[],[f100])).

fof(f22,axiom,(
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

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f108,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f107,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f110,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f111,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f71])).

fof(f117,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f112,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f80])).

fof(f114,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f119,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f71])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f127,plain,(
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
    inference(equality_resolution,[],[f101])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1547,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3237,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1560])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1569,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1559,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3496,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1559])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1566,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9112,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3496,c_1566])).

cnf(c_2071,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2073,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2071])).

cnf(c_2072,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2075,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2072])).

cnf(c_10789,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9112,c_2073,c_2075])).

cnf(c_15,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1563,plain,
    ( k7_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10793,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10789,c_1563])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_10802,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10793,c_12])).

cnf(c_11633,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10802,c_2073,c_2075])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1571,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11642,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11633,c_1571])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1564,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11872,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11642,c_1564])).

cnf(c_13617,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3237,c_11872])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1544,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1554,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6976,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_1554])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2210,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2542,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_2210])).

cnf(c_7902,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6976,c_39,c_37,c_2542])).

cnf(c_6975,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1554])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2205,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0,X1,sK7,X2) = k7_relat_1(sK7,X2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2536,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_7624,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6975,c_36,c_34,c_2536])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1538,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1570,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3521,plain,
    ( k9_subset_1(sK2,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_1538,c_1570])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f128])).

cnf(c_32,plain,
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
    inference(cnf_transformation,[],[f103])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f104])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f105])).

cnf(c_472,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_32,c_31,c_30])).

cnf(c_473,plain,
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
    inference(renaming,[status(thm)],[c_472])).

cnf(c_1534,plain,
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
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_3971,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(sK2,X0,sK4)) != k2_partfun1(sK4,X1,X3,k1_setfam_1(k2_tarski(X0,sK4)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK4),X1,k1_tmap_1(sK2,X1,X0,sK4,X2,X3),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK4,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3521,c_1534])).

cnf(c_4032,plain,
    ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK4))) != k2_partfun1(sK4,X1,X3,k1_setfam_1(k2_tarski(X0,sK4)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK4),X1,k1_tmap_1(sK2,X1,X0,sK4,X2,X3),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK4,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3971,c_3521])).

cnf(c_46,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_47,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_49,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5091,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_2(X3,sK4,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | k2_partfun1(k4_subset_1(sK2,X0,sK4),X1,k1_tmap_1(sK2,X1,X0,sK4,X2,X3),X0) = X2
    | k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK4))) != k2_partfun1(sK4,X1,X3,k1_setfam_1(k2_tarski(X0,sK4)))
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4032,c_47,c_49,c_50])).

cnf(c_5092,plain,
    ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK4))) != k2_partfun1(sK4,X1,X3,k1_setfam_1(k2_tarski(X0,sK4)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK4),X1,k1_tmap_1(sK2,X1,X0,sK4,X2,X3),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK4,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5091])).

cnf(c_7637,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,X0),sK5) = sK7
    | k2_partfun1(sK4,sK3,X0,k1_setfam_1(k2_tarski(sK5,sK4))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK5,sK4)))
    | v1_funct_2(X0,sK4,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7624,c_5092])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_48,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_51,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_52,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_57,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_58,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_59,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11429,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,X0),sK5) = sK7
    | k2_partfun1(sK4,sK3,X0,k1_setfam_1(k2_tarski(sK5,sK4))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK5,sK4)))
    | v1_funct_2(X0,sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7637,c_48,c_51,c_52,c_57,c_58,c_59])).

cnf(c_11430,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,X0),sK5) = sK7
    | k2_partfun1(sK4,sK3,X0,k1_setfam_1(k2_tarski(sK5,sK4))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK5,sK4)))
    | v1_funct_2(X0,sK4,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11429])).

cnf(c_40,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1541,plain,
    ( r1_subset_1(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_17,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1561,plain,
    ( r1_subset_1(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5630,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1561])).

cnf(c_53,plain,
    ( r1_subset_1(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2158,plain,
    ( ~ r1_subset_1(sK4,sK5)
    | r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2159,plain,
    ( r1_subset_1(sK4,sK5) != iProver_top
    | r1_xboole_0(sK4,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_6266,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5630,c_49,c_51,c_53,c_2159])).

cnf(c_6273,plain,
    ( r1_xboole_0(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6266,c_1571])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1573,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6448,plain,
    ( k1_setfam_1(k2_tarski(sK5,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6273,c_1573])).

cnf(c_11435,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,X0),sK5) = sK7
    | k2_partfun1(sK4,sK3,X0,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | v1_funct_2(X0,sK4,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11430,c_6448])).

cnf(c_11444,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,sK6),sK5) = sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7902,c_11435])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_6272,plain,
    ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6266,c_1573])).

cnf(c_1540,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3520,plain,
    ( k9_subset_1(sK2,X0,sK5) = k1_setfam_1(k2_tarski(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_1540,c_1570])).

cnf(c_33,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3773,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(demodulation,[status(thm)],[c_3520,c_33])).

cnf(c_6460,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6272,c_3773])).

cnf(c_7628,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7624,c_6460])).

cnf(c_8500,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7628,c_7902])).

cnf(c_3775,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(sK2,X0,sK5)) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3520,c_1534])).

cnf(c_3836,plain,
    ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3775,c_3520])).

cnf(c_4989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
    | k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3836,c_47,c_51,c_52])).

cnf(c_4990,plain,
    ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4989])).

cnf(c_7635,plain,
    ( k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7624,c_4990])).

cnf(c_11220,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7635,c_48,c_57,c_58,c_59])).

cnf(c_11221,plain,
    ( k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11220])).

cnf(c_11232,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5)))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7902,c_11221])).

cnf(c_11273,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11232,c_6272])).

cnf(c_11287,plain,
    ( ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK4)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11273])).

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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_479,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_32,c_31,c_30])).

cnf(c_480,plain,
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
    inference(renaming,[status(thm)],[c_479])).

cnf(c_1533,plain,
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
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_3777,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(sK2,X0,sK5)) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3520,c_1533])).

cnf(c_3792,plain,
    ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3777,c_3520])).

cnf(c_4860,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
    | k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3792,c_47,c_51,c_52])).

cnf(c_4861,plain,
    ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4860])).

cnf(c_7636,plain,
    ( k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7624,c_4861])).

cnf(c_11360,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7636,c_48,c_57,c_58,c_59])).

cnf(c_11361,plain,
    ( k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11360])).

cnf(c_11372,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5)))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7902,c_11361])).

cnf(c_11413,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11372,c_6272])).

cnf(c_11427,plain,
    ( ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK4)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11413])).

cnf(c_11555,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11444,c_44,c_43,c_39,c_38,c_37,c_8500,c_11287,c_11427])).

cnf(c_13787,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13617,c_11555])).

cnf(c_3238,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_1560])).

cnf(c_13618,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3238,c_11872])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13787,c_13618])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.70/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.01  
% 3.70/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.01  
% 3.70/1.01  ------  iProver source info
% 3.70/1.01  
% 3.70/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.01  git: non_committed_changes: false
% 3.70/1.01  git: last_make_outside_of_git: false
% 3.70/1.01  
% 3.70/1.01  ------ 
% 3.70/1.01  ------ Parsing...
% 3.70/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.01  ------ Proving...
% 3.70/1.01  ------ Problem Properties 
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  clauses                                 47
% 3.70/1.01  conjectures                             14
% 3.70/1.01  EPR                                     14
% 3.70/1.01  Horn                                    35
% 3.70/1.01  unary                                   17
% 3.70/1.01  binary                                  12
% 3.70/1.01  lits                                    167
% 3.70/1.01  lits eq                                 22
% 3.70/1.01  fd_pure                                 0
% 3.70/1.01  fd_pseudo                               0
% 3.70/1.01  fd_cond                                 3
% 3.70/1.01  fd_pseudo_cond                          1
% 3.70/1.01  AC symbols                              0
% 3.70/1.01  
% 3.70/1.01  ------ Input Options Time Limit: Unbounded
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  ------ 
% 3.70/1.01  Current options:
% 3.70/1.01  ------ 
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  ------ Proving...
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  % SZS status Theorem for theBenchmark.p
% 3.70/1.01  
% 3.70/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.01  
% 3.70/1.01  fof(f23,conjecture,(
% 3.70/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f24,negated_conjecture,(
% 3.70/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.70/1.01    inference(negated_conjecture,[],[f23])).
% 3.70/1.01  
% 3.70/1.01  fof(f51,plain,(
% 3.70/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.70/1.01    inference(ennf_transformation,[],[f24])).
% 3.70/1.01  
% 3.70/1.01  fof(f52,plain,(
% 3.70/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.70/1.01    inference(flattening,[],[f51])).
% 3.70/1.01  
% 3.70/1.01  fof(f70,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 3.70/1.01    introduced(choice_axiom,[])).
% 3.70/1.01  
% 3.70/1.01  fof(f69,plain,(
% 3.70/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 3.70/1.01    introduced(choice_axiom,[])).
% 3.70/1.01  
% 3.70/1.01  fof(f68,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 3.70/1.01    introduced(choice_axiom,[])).
% 3.70/1.01  
% 3.70/1.01  fof(f67,plain,(
% 3.70/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 3.70/1.01    introduced(choice_axiom,[])).
% 3.70/1.01  
% 3.70/1.01  fof(f66,plain,(
% 3.70/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 3.70/1.01    introduced(choice_axiom,[])).
% 3.70/1.01  
% 3.70/1.01  fof(f65,plain,(
% 3.70/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 3.70/1.01    introduced(choice_axiom,[])).
% 3.70/1.01  
% 3.70/1.01  fof(f71,plain,(
% 3.70/1.01    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.70/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f52,f70,f69,f68,f67,f66,f65])).
% 3.70/1.01  
% 3.70/1.01  fof(f118,plain,(
% 3.70/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f15,axiom,(
% 3.70/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f38,plain,(
% 3.70/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.01    inference(ennf_transformation,[],[f15])).
% 3.70/1.01  
% 3.70/1.01  fof(f91,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.01    inference(cnf_transformation,[],[f38])).
% 3.70/1.01  
% 3.70/1.01  fof(f6,axiom,(
% 3.70/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f79,plain,(
% 3.70/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.70/1.01    inference(cnf_transformation,[],[f6])).
% 3.70/1.01  
% 3.70/1.01  fof(f16,axiom,(
% 3.70/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f26,plain,(
% 3.70/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.70/1.01    inference(pure_predicate_removal,[],[f16])).
% 3.70/1.01  
% 3.70/1.01  fof(f39,plain,(
% 3.70/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.01    inference(ennf_transformation,[],[f26])).
% 3.70/1.01  
% 3.70/1.01  fof(f92,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.01    inference(cnf_transformation,[],[f39])).
% 3.70/1.01  
% 3.70/1.01  fof(f10,axiom,(
% 3.70/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f32,plain,(
% 3.70/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.70/1.01    inference(ennf_transformation,[],[f10])).
% 3.70/1.01  
% 3.70/1.01  fof(f33,plain,(
% 3.70/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.70/1.01    inference(flattening,[],[f32])).
% 3.70/1.01  
% 3.70/1.01  fof(f83,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f33])).
% 3.70/1.01  
% 3.70/1.01  fof(f13,axiom,(
% 3.70/1.01    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f35,plain,(
% 3.70/1.01    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.70/1.01    inference(ennf_transformation,[],[f13])).
% 3.70/1.01  
% 3.70/1.01  fof(f58,plain,(
% 3.70/1.01    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.70/1.01    inference(nnf_transformation,[],[f35])).
% 3.70/1.01  
% 3.70/1.01  fof(f87,plain,(
% 3.70/1.01    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f58])).
% 3.70/1.01  
% 3.70/1.01  fof(f11,axiom,(
% 3.70/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f84,plain,(
% 3.70/1.01    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.70/1.01    inference(cnf_transformation,[],[f11])).
% 3.70/1.01  
% 3.70/1.01  fof(f4,axiom,(
% 3.70/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f27,plain,(
% 3.70/1.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.70/1.01    inference(ennf_transformation,[],[f4])).
% 3.70/1.01  
% 3.70/1.01  fof(f77,plain,(
% 3.70/1.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f27])).
% 3.70/1.01  
% 3.70/1.01  fof(f88,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f58])).
% 3.70/1.01  
% 3.70/1.01  fof(f115,plain,(
% 3.70/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f19,axiom,(
% 3.70/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f43,plain,(
% 3.70/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.70/1.01    inference(ennf_transformation,[],[f19])).
% 3.70/1.01  
% 3.70/1.01  fof(f44,plain,(
% 3.70/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.70/1.01    inference(flattening,[],[f43])).
% 3.70/1.01  
% 3.70/1.01  fof(f97,plain,(
% 3.70/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f44])).
% 3.70/1.01  
% 3.70/1.01  fof(f113,plain,(
% 3.70/1.01    v1_funct_1(sK6)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f116,plain,(
% 3.70/1.01    v1_funct_1(sK7)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f109,plain,(
% 3.70/1.01    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f5,axiom,(
% 3.70/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f28,plain,(
% 3.70/1.01    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.70/1.01    inference(ennf_transformation,[],[f5])).
% 3.70/1.01  
% 3.70/1.01  fof(f78,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.70/1.01    inference(cnf_transformation,[],[f28])).
% 3.70/1.01  
% 3.70/1.01  fof(f7,axiom,(
% 3.70/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f80,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.70/1.01    inference(cnf_transformation,[],[f7])).
% 3.70/1.01  
% 3.70/1.01  fof(f122,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.70/1.01    inference(definition_unfolding,[],[f78,f80])).
% 3.70/1.01  
% 3.70/1.01  fof(f21,axiom,(
% 3.70/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f47,plain,(
% 3.70/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/1.01    inference(ennf_transformation,[],[f21])).
% 3.70/1.01  
% 3.70/1.01  fof(f48,plain,(
% 3.70/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/1.01    inference(flattening,[],[f47])).
% 3.70/1.01  
% 3.70/1.01  fof(f63,plain,(
% 3.70/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/1.01    inference(nnf_transformation,[],[f48])).
% 3.70/1.01  
% 3.70/1.01  fof(f64,plain,(
% 3.70/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/1.01    inference(flattening,[],[f63])).
% 3.70/1.01  
% 3.70/1.01  fof(f100,plain,(
% 3.70/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f64])).
% 3.70/1.01  
% 3.70/1.01  fof(f128,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.01    inference(equality_resolution,[],[f100])).
% 3.70/1.01  
% 3.70/1.01  fof(f22,axiom,(
% 3.70/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f49,plain,(
% 3.70/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.70/1.01    inference(ennf_transformation,[],[f22])).
% 3.70/1.01  
% 3.70/1.01  fof(f50,plain,(
% 3.70/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.70/1.01    inference(flattening,[],[f49])).
% 3.70/1.01  
% 3.70/1.01  fof(f103,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f50])).
% 3.70/1.01  
% 3.70/1.01  fof(f104,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f50])).
% 3.70/1.01  
% 3.70/1.01  fof(f105,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f50])).
% 3.70/1.01  
% 3.70/1.01  fof(f106,plain,(
% 3.70/1.01    ~v1_xboole_0(sK2)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f108,plain,(
% 3.70/1.01    ~v1_xboole_0(sK4)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f107,plain,(
% 3.70/1.01    ~v1_xboole_0(sK3)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f110,plain,(
% 3.70/1.01    ~v1_xboole_0(sK5)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f111,plain,(
% 3.70/1.01    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f117,plain,(
% 3.70/1.01    v1_funct_2(sK7,sK5,sK3)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f112,plain,(
% 3.70/1.01    r1_subset_1(sK4,sK5)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f14,axiom,(
% 3.70/1.01    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f36,plain,(
% 3.70/1.01    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.70/1.01    inference(ennf_transformation,[],[f14])).
% 3.70/1.01  
% 3.70/1.01  fof(f37,plain,(
% 3.70/1.01    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.70/1.01    inference(flattening,[],[f36])).
% 3.70/1.01  
% 3.70/1.01  fof(f59,plain,(
% 3.70/1.01    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.70/1.01    inference(nnf_transformation,[],[f37])).
% 3.70/1.01  
% 3.70/1.01  fof(f89,plain,(
% 3.70/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f59])).
% 3.70/1.01  
% 3.70/1.01  fof(f2,axiom,(
% 3.70/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.70/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f57,plain,(
% 3.70/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.70/1.01    inference(nnf_transformation,[],[f2])).
% 3.70/1.01  
% 3.70/1.01  fof(f74,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f57])).
% 3.70/1.01  
% 3.70/1.01  fof(f121,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.70/1.01    inference(definition_unfolding,[],[f74,f80])).
% 3.70/1.01  
% 3.70/1.01  fof(f114,plain,(
% 3.70/1.01    v1_funct_2(sK6,sK4,sK3)),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f119,plain,(
% 3.70/1.01    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 3.70/1.01    inference(cnf_transformation,[],[f71])).
% 3.70/1.01  
% 3.70/1.01  fof(f101,plain,(
% 3.70/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f64])).
% 3.70/1.01  
% 3.70/1.01  fof(f127,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.01    inference(equality_resolution,[],[f101])).
% 3.70/1.01  
% 3.70/1.01  cnf(c_34,negated_conjecture,
% 3.70/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 3.70/1.01      inference(cnf_transformation,[],[f118]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1547,plain,
% 3.70/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_18,plain,
% 3.70/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.01      | v1_relat_1(X0) ),
% 3.70/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1560,plain,
% 3.70/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.70/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_3237,plain,
% 3.70/1.01      ( v1_relat_1(sK7) = iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_1547,c_1560]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_7,plain,
% 3.70/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.70/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1569,plain,
% 3.70/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_19,plain,
% 3.70/1.01      ( v4_relat_1(X0,X1)
% 3.70/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.70/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1559,plain,
% 3.70/1.01      ( v4_relat_1(X0,X1) = iProver_top
% 3.70/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_3496,plain,
% 3.70/1.01      ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_1569,c_1559]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_10,plain,
% 3.70/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.70/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1566,plain,
% 3.70/1.01      ( k7_relat_1(X0,X1) = X0
% 3.70/1.01      | v4_relat_1(X0,X1) != iProver_top
% 3.70/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_9112,plain,
% 3.70/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.70/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_3496,c_1566]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_2071,plain,
% 3.70/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.70/1.01      | v1_relat_1(k1_xboole_0) ),
% 3.70/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_2073,plain,
% 3.70/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_2071]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_2072,plain,
% 3.70/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.70/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_2075,plain,
% 3.70/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_2072]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_10789,plain,
% 3.70/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.70/1.01      inference(global_propositional_subsumption,
% 3.70/1.01                [status(thm)],
% 3.70/1.01                [c_9112,c_2073,c_2075]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_15,plain,
% 3.70/1.01      ( r1_xboole_0(k1_relat_1(X0),X1)
% 3.70/1.01      | ~ v1_relat_1(X0)
% 3.70/1.01      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 3.70/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1563,plain,
% 3.70/1.01      ( k7_relat_1(X0,X1) != k1_xboole_0
% 3.70/1.01      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 3.70/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_10793,plain,
% 3.70/1.01      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 3.70/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_10789,c_1563]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_12,plain,
% 3.70/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.70/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_10802,plain,
% 3.70/1.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
% 3.70/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.70/1.01      inference(light_normalisation,[status(thm)],[c_10793,c_12]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_11633,plain,
% 3.70/1.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.70/1.01      inference(global_propositional_subsumption,
% 3.70/1.01                [status(thm)],
% 3.70/1.01                [c_10802,c_2073,c_2075]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_5,plain,
% 3.70/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.70/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1571,plain,
% 3.70/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 3.70/1.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_11642,plain,
% 3.70/1.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_11633,c_1571]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_14,plain,
% 3.70/1.01      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 3.70/1.01      | ~ v1_relat_1(X0)
% 3.70/1.01      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 3.70/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1564,plain,
% 3.70/1.01      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.70/1.01      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 3.70/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_11872,plain,
% 3.70/1.01      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.70/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_11642,c_1564]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_13617,plain,
% 3.70/1.01      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_3237,c_11872]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_37,negated_conjecture,
% 3.70/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.70/1.01      inference(cnf_transformation,[],[f115]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1544,plain,
% 3.70/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_24,plain,
% 3.70/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.01      | ~ v1_funct_1(X0)
% 3.70/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.70/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1554,plain,
% 3.70/1.01      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.70/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_6976,plain,
% 3.70/1.01      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
% 3.70/1.01      | v1_funct_1(sK6) != iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_1544,c_1554]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_39,negated_conjecture,
% 3.70/1.01      ( v1_funct_1(sK6) ),
% 3.70/1.01      inference(cnf_transformation,[],[f113]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_2210,plain,
% 3.70/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.70/1.01      | ~ v1_funct_1(sK6)
% 3.70/1.01      | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
% 3.70/1.01      inference(instantiation,[status(thm)],[c_24]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_2542,plain,
% 3.70/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.70/1.01      | ~ v1_funct_1(sK6)
% 3.70/1.01      | k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.70/1.01      inference(instantiation,[status(thm)],[c_2210]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_7902,plain,
% 3.70/1.01      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.70/1.01      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_6976,c_39,c_37,c_2542]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_6975,plain,
% 3.70/1.02      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
% 3.70/1.02      | v1_funct_1(sK7) != iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_1547,c_1554]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_36,negated_conjecture,
% 3.70/1.02      ( v1_funct_1(sK7) ),
% 3.70/1.02      inference(cnf_transformation,[],[f116]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_2205,plain,
% 3.70/1.02      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.70/1.02      | ~ v1_funct_1(sK7)
% 3.70/1.02      | k2_partfun1(X0,X1,sK7,X2) = k7_relat_1(sK7,X2) ),
% 3.70/1.02      inference(instantiation,[status(thm)],[c_24]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_2536,plain,
% 3.70/1.02      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 3.70/1.02      | ~ v1_funct_1(sK7)
% 3.70/1.02      | k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
% 3.70/1.02      inference(instantiation,[status(thm)],[c_2205]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_7624,plain,
% 3.70/1.02      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_6975,c_36,c_34,c_2536]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_43,negated_conjecture,
% 3.70/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 3.70/1.02      inference(cnf_transformation,[],[f109]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_1538,plain,
% 3.70/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_6,plain,
% 3.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.70/1.02      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.70/1.02      inference(cnf_transformation,[],[f122]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_1570,plain,
% 3.70/1.02      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3521,plain,
% 3.70/1.02      ( k9_subset_1(sK2,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_1538,c_1570]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_29,plain,
% 3.70/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_1(X3)
% 3.70/1.02      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X1)
% 3.70/1.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/1.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.70/1.02      inference(cnf_transformation,[],[f128]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_32,plain,
% 3.70/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_1(X3)
% 3.70/1.02      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X1) ),
% 3.70/1.02      inference(cnf_transformation,[],[f103]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_31,plain,
% 3.70/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_1(X3)
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X1) ),
% 3.70/1.02      inference(cnf_transformation,[],[f104]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_30,plain,
% 3.70/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_1(X3)
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X1) ),
% 3.70/1.02      inference(cnf_transformation,[],[f105]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_472,plain,
% 3.70/1.02      ( ~ v1_funct_1(X3)
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X1)
% 3.70/1.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/1.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_29,c_32,c_31,c_30]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_473,plain,
% 3.70/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_1(X3)
% 3.70/1.02      | v1_xboole_0(X1)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/1.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.70/1.02      inference(renaming,[status(thm)],[c_472]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_1534,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.70/1.02      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_funct_1(X5) != iProver_top
% 3.70/1.02      | v1_xboole_0(X3) = iProver_top
% 3.70/1.02      | v1_xboole_0(X4) = iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3971,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k9_subset_1(sK2,X0,sK4)) != k2_partfun1(sK4,X1,X3,k1_setfam_1(k2_tarski(X0,sK4)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK4),X1,k1_tmap_1(sK2,X1,X0,sK4,X2,X3),X0) = X2
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK4,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK4) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_3521,c_1534]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_4032,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK4))) != k2_partfun1(sK4,X1,X3,k1_setfam_1(k2_tarski(X0,sK4)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK4),X1,k1_tmap_1(sK2,X1,X0,sK4,X2,X3),X0) = X2
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK4,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK4) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/1.02      inference(light_normalisation,[status(thm)],[c_3971,c_3521]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_46,negated_conjecture,
% 3.70/1.02      ( ~ v1_xboole_0(sK2) ),
% 3.70/1.02      inference(cnf_transformation,[],[f106]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_47,plain,
% 3.70/1.02      ( v1_xboole_0(sK2) != iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_44,negated_conjecture,
% 3.70/1.02      ( ~ v1_xboole_0(sK4) ),
% 3.70/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_49,plain,
% 3.70/1.02      ( v1_xboole_0(sK4) != iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_50,plain,
% 3.70/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_5091,plain,
% 3.70/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK4,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK4),X1,k1_tmap_1(sK2,X1,X0,sK4,X2,X3),X0) = X2
% 3.70/1.02      | k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK4))) != k2_partfun1(sK4,X1,X3,k1_setfam_1(k2_tarski(X0,sK4)))
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_4032,c_47,c_49,c_50]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_5092,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK4))) != k2_partfun1(sK4,X1,X3,k1_setfam_1(k2_tarski(X0,sK4)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK4),X1,k1_tmap_1(sK2,X1,X0,sK4,X2,X3),X0) = X2
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK4,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(renaming,[status(thm)],[c_5091]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_7637,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,X0),sK5) = sK7
% 3.70/1.02      | k2_partfun1(sK4,sK3,X0,k1_setfam_1(k2_tarski(sK5,sK4))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK5,sK4)))
% 3.70/1.02      | v1_funct_2(X0,sK4,sK3) != iProver_top
% 3.70/1.02      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X0) != iProver_top
% 3.70/1.02      | v1_funct_1(sK7) != iProver_top
% 3.70/1.02      | v1_xboole_0(sK3) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_7624,c_5092]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_45,negated_conjecture,
% 3.70/1.02      ( ~ v1_xboole_0(sK3) ),
% 3.70/1.02      inference(cnf_transformation,[],[f107]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_48,plain,
% 3.70/1.02      ( v1_xboole_0(sK3) != iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_42,negated_conjecture,
% 3.70/1.02      ( ~ v1_xboole_0(sK5) ),
% 3.70/1.02      inference(cnf_transformation,[],[f110]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_51,plain,
% 3.70/1.02      ( v1_xboole_0(sK5) != iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_41,negated_conjecture,
% 3.70/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 3.70/1.02      inference(cnf_transformation,[],[f111]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_52,plain,
% 3.70/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_57,plain,
% 3.70/1.02      ( v1_funct_1(sK7) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_35,negated_conjecture,
% 3.70/1.02      ( v1_funct_2(sK7,sK5,sK3) ),
% 3.70/1.02      inference(cnf_transformation,[],[f117]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_58,plain,
% 3.70/1.02      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_59,plain,
% 3.70/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11429,plain,
% 3.70/1.02      ( v1_funct_1(X0) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,X0),sK5) = sK7
% 3.70/1.02      | k2_partfun1(sK4,sK3,X0,k1_setfam_1(k2_tarski(sK5,sK4))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK5,sK4)))
% 3.70/1.02      | v1_funct_2(X0,sK4,sK3) != iProver_top ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_7637,c_48,c_51,c_52,c_57,c_58,c_59]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11430,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,X0),sK5) = sK7
% 3.70/1.02      | k2_partfun1(sK4,sK3,X0,k1_setfam_1(k2_tarski(sK5,sK4))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK5,sK4)))
% 3.70/1.02      | v1_funct_2(X0,sK4,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.70/1.02      inference(renaming,[status(thm)],[c_11429]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_40,negated_conjecture,
% 3.70/1.02      ( r1_subset_1(sK4,sK5) ),
% 3.70/1.02      inference(cnf_transformation,[],[f112]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_1541,plain,
% 3.70/1.02      ( r1_subset_1(sK4,sK5) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_17,plain,
% 3.70/1.02      ( ~ r1_subset_1(X0,X1)
% 3.70/1.02      | r1_xboole_0(X0,X1)
% 3.70/1.02      | v1_xboole_0(X0)
% 3.70/1.02      | v1_xboole_0(X1) ),
% 3.70/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_1561,plain,
% 3.70/1.02      ( r1_subset_1(X0,X1) != iProver_top
% 3.70/1.02      | r1_xboole_0(X0,X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_5630,plain,
% 3.70/1.02      ( r1_xboole_0(sK4,sK5) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_1541,c_1561]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_53,plain,
% 3.70/1.02      ( r1_subset_1(sK4,sK5) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_2158,plain,
% 3.70/1.02      ( ~ r1_subset_1(sK4,sK5)
% 3.70/1.02      | r1_xboole_0(sK4,sK5)
% 3.70/1.02      | v1_xboole_0(sK5)
% 3.70/1.02      | v1_xboole_0(sK4) ),
% 3.70/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_2159,plain,
% 3.70/1.02      ( r1_subset_1(sK4,sK5) != iProver_top
% 3.70/1.02      | r1_xboole_0(sK4,sK5) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_2158]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_6266,plain,
% 3.70/1.02      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_5630,c_49,c_51,c_53,c_2159]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_6273,plain,
% 3.70/1.02      ( r1_xboole_0(sK5,sK4) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_6266,c_1571]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3,plain,
% 3.70/1.02      ( ~ r1_xboole_0(X0,X1)
% 3.70/1.02      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 3.70/1.02      inference(cnf_transformation,[],[f121]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_1573,plain,
% 3.70/1.02      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 3.70/1.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_6448,plain,
% 3.70/1.02      ( k1_setfam_1(k2_tarski(sK5,sK4)) = k1_xboole_0 ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_6273,c_1573]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11435,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,X0),sK5) = sK7
% 3.70/1.02      | k2_partfun1(sK4,sK3,X0,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 3.70/1.02      | v1_funct_2(X0,sK4,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.70/1.02      inference(light_normalisation,[status(thm)],[c_11430,c_6448]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11444,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK5,sK4),sK3,k1_tmap_1(sK2,sK3,sK5,sK4,sK7,sK6),sK5) = sK7
% 3.70/1.02      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 3.70/1.02      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_7902,c_11435]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_38,negated_conjecture,
% 3.70/1.02      ( v1_funct_2(sK6,sK4,sK3) ),
% 3.70/1.02      inference(cnf_transformation,[],[f114]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_6272,plain,
% 3.70/1.02      ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_6266,c_1573]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_1540,plain,
% 3.70/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3520,plain,
% 3.70/1.02      ( k9_subset_1(sK2,X0,sK5) = k1_setfam_1(k2_tarski(X0,sK5)) ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_1540,c_1570]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_33,negated_conjecture,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/1.02      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.70/1.02      inference(cnf_transformation,[],[f119]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3773,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/1.02      | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 3.70/1.02      inference(demodulation,[status(thm)],[c_3520,c_33]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_6460,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/1.02      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
% 3.70/1.02      inference(demodulation,[status(thm)],[c_6272,c_3773]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_7628,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/1.02      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.70/1.02      inference(demodulation,[status(thm)],[c_7624,c_6460]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_8500,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/1.02      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.70/1.02      inference(demodulation,[status(thm)],[c_7628,c_7902]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3775,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k9_subset_1(sK2,X0,sK5)) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_3520,c_1534]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3836,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/1.02      inference(light_normalisation,[status(thm)],[c_3775,c_3520]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_4989,plain,
% 3.70/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
% 3.70/1.02      | k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_3836,c_47,c_51,c_52]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_4990,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(renaming,[status(thm)],[c_4989]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_7635,plain,
% 3.70/1.02      ( k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.70/1.02      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/1.02      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.70/1.02      | v1_funct_1(X1) != iProver_top
% 3.70/1.02      | v1_funct_1(sK7) != iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_7624,c_4990]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11220,plain,
% 3.70/1.02      ( v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/1.02      | k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.70/1.02      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_7635,c_48,c_57,c_58,c_59]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11221,plain,
% 3.70/1.02      ( k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.70/1.02      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X1) != iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(renaming,[status(thm)],[c_11220]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11232,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.70/1.02      | k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5)))
% 3.70/1.02      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(sK6) != iProver_top
% 3.70/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_7902,c_11221]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11273,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.70/1.02      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 3.70/1.02      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(sK6) != iProver_top
% 3.70/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.02      inference(light_normalisation,[status(thm)],[c_11232,c_6272]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11287,plain,
% 3.70/1.02      ( ~ v1_funct_2(sK6,sK4,sK3)
% 3.70/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.70/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 3.70/1.02      | ~ v1_funct_1(sK6)
% 3.70/1.02      | v1_xboole_0(sK4)
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.70/1.02      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.70/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_11273]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_28,plain,
% 3.70/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_1(X3)
% 3.70/1.02      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X1)
% 3.70/1.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/1.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.70/1.02      inference(cnf_transformation,[],[f127]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_479,plain,
% 3.70/1.02      ( ~ v1_funct_1(X3)
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X1)
% 3.70/1.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/1.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_28,c_32,c_31,c_30]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_480,plain,
% 3.70/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.02      | ~ v1_funct_2(X3,X4,X2)
% 3.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/1.02      | ~ v1_funct_1(X0)
% 3.70/1.02      | ~ v1_funct_1(X3)
% 3.70/1.02      | v1_xboole_0(X1)
% 3.70/1.02      | v1_xboole_0(X2)
% 3.70/1.02      | v1_xboole_0(X4)
% 3.70/1.02      | v1_xboole_0(X5)
% 3.70/1.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/1.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.70/1.02      inference(renaming,[status(thm)],[c_479]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_1533,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.70/1.02      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_funct_1(X5) != iProver_top
% 3.70/1.02      | v1_xboole_0(X3) = iProver_top
% 3.70/1.02      | v1_xboole_0(X4) = iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3777,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k9_subset_1(sK2,X0,sK5)) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_3520,c_1533]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3792,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/1.02      inference(light_normalisation,[status(thm)],[c_3777,c_3520]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_4860,plain,
% 3.70/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
% 3.70/1.02      | k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_3792,c_47,c_51,c_52]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_4861,plain,
% 3.70/1.02      ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK5))) != k2_partfun1(sK5,X1,X3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
% 3.70/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.02      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X3) != iProver_top
% 3.70/1.02      | v1_funct_1(X2) != iProver_top
% 3.70/1.02      | v1_xboole_0(X1) = iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(renaming,[status(thm)],[c_4860]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_7636,plain,
% 3.70/1.02      ( k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.70/1.02      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/1.02      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.70/1.02      | v1_funct_1(X1) != iProver_top
% 3.70/1.02      | v1_funct_1(sK7) != iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_7624,c_4861]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11360,plain,
% 3.70/1.02      ( v1_xboole_0(X0) = iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/1.02      | k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.70/1.02      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_7636,c_48,c_57,c_58,c_59]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11361,plain,
% 3.70/1.02      ( k2_partfun1(X0,sK3,X1,k1_setfam_1(k2_tarski(X0,sK5))) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.70/1.02      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(X1) != iProver_top
% 3.70/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.02      inference(renaming,[status(thm)],[c_11360]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11372,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.70/1.02      | k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5)))
% 3.70/1.02      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(sK6) != iProver_top
% 3.70/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_7902,c_11361]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11413,plain,
% 3.70/1.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.70/1.02      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 3.70/1.02      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/1.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/1.02      | v1_funct_1(sK6) != iProver_top
% 3.70/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.02      inference(light_normalisation,[status(thm)],[c_11372,c_6272]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11427,plain,
% 3.70/1.02      ( ~ v1_funct_2(sK6,sK4,sK3)
% 3.70/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.70/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 3.70/1.02      | ~ v1_funct_1(sK6)
% 3.70/1.02      | v1_xboole_0(sK4)
% 3.70/1.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.70/1.02      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.70/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_11413]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_11555,plain,
% 3.70/1.02      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.70/1.02      inference(global_propositional_subsumption,
% 3.70/1.02                [status(thm)],
% 3.70/1.02                [c_11444,c_44,c_43,c_39,c_38,c_37,c_8500,c_11287,c_11427]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_13787,plain,
% 3.70/1.02      ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.70/1.02      inference(demodulation,[status(thm)],[c_13617,c_11555]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_3238,plain,
% 3.70/1.02      ( v1_relat_1(sK6) = iProver_top ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_1544,c_1560]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(c_13618,plain,
% 3.70/1.02      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.70/1.02      inference(superposition,[status(thm)],[c_3238,c_11872]) ).
% 3.70/1.02  
% 3.70/1.02  cnf(contradiction,plain,
% 3.70/1.02      ( $false ),
% 3.70/1.02      inference(minisat,[status(thm)],[c_13787,c_13618]) ).
% 3.70/1.02  
% 3.70/1.02  
% 3.70/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.02  
% 3.70/1.02  ------                               Statistics
% 3.70/1.02  
% 3.70/1.02  ------ Selected
% 3.70/1.02  
% 3.70/1.02  total_time:                             0.504
% 3.70/1.02  
%------------------------------------------------------------------------------
