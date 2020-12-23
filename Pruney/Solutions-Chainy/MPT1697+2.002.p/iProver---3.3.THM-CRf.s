%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:21 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  227 (1032 expanded)
%              Number of clauses        :  132 ( 263 expanded)
%              Number of leaves         :   28 ( 378 expanded)
%              Depth                    :   22
%              Number of atoms          : 1237 (11887 expanded)
%              Number of equality atoms :  331 (2727 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

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

fof(f63,plain,(
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

fof(f62,plain,(
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

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f64,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f48,f63,f62,f61,f60,f59,f58])).

fof(f107,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f64])).

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

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f105,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK1(X1,X2)) != k1_funct_1(X2,sK1(X1,X2))
        & r2_hidden(sK1(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ( k1_funct_1(X1,sK1(X1,X2)) != k1_funct_1(X2,sK1(X1,X2))
            & r2_hidden(sK1(X1,X2),k1_relat_1(X1)) )
          | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f53])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | r2_hidden(sK1(X1,X2),k1_relat_1(X1))
      | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f50])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f99,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f64])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f64])).

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

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f108,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f95,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f64])).

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

fof(f56,plain,(
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
    inference(flattening,[],[f56])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
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
    inference(equality_resolution,[],[f89])).

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

fof(f92,plain,(
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

fof(f93,plain,(
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

fof(f94,plain,(
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

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f112,plain,(
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
    inference(equality_resolution,[],[f90])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2169,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_535,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_18,c_22])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_22,c_18,c_17])).

cnf(c_540,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_593,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_19,c_540])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_22,c_19,c_18,c_17])).

cnf(c_598,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_597])).

cnf(c_2154,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_3008,plain,
    ( k1_relat_1(sK7) = sK5
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_2154])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2433,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(X1)
    | k1_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_2664,plain,
    ( ~ v1_funct_2(sK7,sK5,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK3)
    | k1_relat_1(sK7) = sK5 ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_6618,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3008,c_42,c_33,c_32,c_31,c_2664])).

cnf(c_16,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k7_relat_1(X1,X2) = X0
    | k3_xboole_0(k1_relat_1(X1),X2) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2176,plain,
    ( k7_relat_1(X0,X1) = X2
    | k3_xboole_0(k1_relat_1(X0),X1) != k1_relat_1(X2)
    | r2_hidden(sK1(X2,X0),k1_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6622,plain,
    ( k7_relat_1(sK7,X0) = X1
    | k3_xboole_0(sK5,X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,sK7),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6618,c_2176])).

cnf(c_54,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_56,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2313,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2314,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2313])).

cnf(c_9084,plain,
    ( v1_funct_1(X1) != iProver_top
    | k7_relat_1(sK7,X0) = X1
    | k3_xboole_0(sK5,X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,sK7),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6622,c_54,c_56,c_2314])).

cnf(c_9085,plain,
    ( k7_relat_1(sK7,X0) = X1
    | k3_xboole_0(sK5,X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,sK7),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9084])).

cnf(c_9090,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = X0
    | k1_relat_1(X0) != k1_xboole_0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_9085])).

cnf(c_9095,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,sK7),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_9090])).

cnf(c_2175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3147,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_2175])).

cnf(c_3787,plain,
    ( k7_relat_1(X0,k1_xboole_0) = X1
    | k1_relat_1(X1) != k1_xboole_0
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2176])).

cnf(c_3796,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_3787])).

cnf(c_2303,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2305,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2303])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2304,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2309,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2304])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | ~ v1_relat_1(sK7)
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2878,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK7)
    | v1_funct_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_2880,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2878])).

cnf(c_2879,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2882,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2879])).

cnf(c_4055,plain,
    ( v1_funct_1(X0) != iProver_top
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3796,c_54,c_56,c_2305,c_2309,c_2314,c_2880,c_2882])).

cnf(c_4056,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4055])).

cnf(c_4061,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_4056])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2183,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2185,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3239,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2185])).

cnf(c_3334,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_3239])).

cnf(c_4977,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4061,c_3334])).

cnf(c_7872,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3147,c_4977])).

cnf(c_9729,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9095,c_54,c_7872])).

cnf(c_14,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_580,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_37])).

cnf(c_581,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_583,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_581,c_41,c_39])).

cnf(c_2155,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2186,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3102,plain,
    ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2155,c_2186])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2163,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2182,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3342,plain,
    ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_2163,c_2182])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2166,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2174,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3646,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_2174])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2428,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2659,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_2428])).

cnf(c_7374,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3646,c_36,c_34,c_2659])).

cnf(c_3645,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_2174])).

cnf(c_2423,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0,X1,sK7,X2) = k7_relat_1(sK7,X2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2654,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_2423])).

cnf(c_7269,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3645,c_33,c_31,c_2654])).

cnf(c_30,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_7272,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_7269,c_30])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1282,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2345,plain,
    ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != X0
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != X0
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_2583,plain,
    ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2345])).

cnf(c_1281,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2584,plain,
    ( k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_2870,plain,
    ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != X0
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_4096,plain,
    ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2870])).

cnf(c_4097,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2654])).

cnf(c_26,plain,
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
    inference(cnf_transformation,[],[f113])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f92])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f93])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f94])).

cnf(c_228,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_29,c_28,c_27])).

cnf(c_229,plain,
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
    inference(renaming,[status(thm)],[c_228])).

cnf(c_2514,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK6,k9_subset_1(X4,X3,X1))
    | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK6,X0),X3) = sK6 ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_2806,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ v1_funct_2(sK6,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | k2_partfun1(X0,X1,sK7,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK6,k9_subset_1(X3,X2,X0))
    | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK6,sK7),X2) = sK6 ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_3308,plain,
    ( ~ v1_funct_2(sK7,X0,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK4)
    | k2_partfun1(X0,sK3,sK7,k9_subset_1(X1,sK4,X0)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X1,sK4,X0))
    | k2_partfun1(k4_subset_1(X1,sK4,X0),sK3,k1_tmap_1(X1,sK3,sK4,X0,sK6,sK7),sK4) = sK6 ),
    inference(instantiation,[status(thm)],[c_2806])).

cnf(c_3604,plain,
    ( ~ v1_funct_2(sK7,sK5,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(X0,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X0,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3308])).

cnf(c_4915,plain,
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
    inference(instantiation,[status(thm)],[c_3604])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f112])).

cnf(c_235,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_29,c_28,c_27])).

cnf(c_236,plain,
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
    inference(renaming,[status(thm)],[c_235])).

cnf(c_2524,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK6,k9_subset_1(X4,X3,X1))
    | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK6,X0),X1) = X0 ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_2824,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ v1_funct_2(sK6,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | k2_partfun1(X0,X1,sK7,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK6,k9_subset_1(X3,X2,X0))
    | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK6,sK7),X0) = sK7 ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_3328,plain,
    ( ~ v1_funct_2(sK7,X0,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK4)
    | k2_partfun1(X0,sK3,sK7,k9_subset_1(X1,sK4,X0)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X1,sK4,X0))
    | k2_partfun1(k4_subset_1(X1,sK4,X0),sK3,k1_tmap_1(X1,sK3,sK4,X0,sK6,sK7),X0) = sK7 ),
    inference(instantiation,[status(thm)],[c_2824])).

cnf(c_3626,plain,
    ( ~ v1_funct_2(sK7,sK5,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(X0,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X0,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3328])).

cnf(c_4927,plain,
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
    inference(instantiation,[status(thm)],[c_3626])).

cnf(c_7370,plain,
    ( k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7272,c_43,c_42,c_41,c_40,c_39,c_38,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_2583,c_2584,c_4096,c_4097,c_4915,c_4927])).

cnf(c_7377,plain,
    ( k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_7374,c_7370])).

cnf(c_19879,plain,
    ( k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_3342,c_7377])).

cnf(c_20159,plain,
    ( k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_3342,c_19879])).

cnf(c_20160,plain,
    ( k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3102,c_20159])).

cnf(c_20233,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3102,c_20160])).

cnf(c_20449,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9729,c_20233])).

cnf(c_3148,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_2175])).

cnf(c_7873,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3148,c_4977])).

cnf(c_51,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20449,c_7873,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.95/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/1.51  
% 7.95/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.95/1.51  
% 7.95/1.51  ------  iProver source info
% 7.95/1.51  
% 7.95/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.95/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.95/1.51  git: non_committed_changes: false
% 7.95/1.51  git: last_make_outside_of_git: false
% 7.95/1.51  
% 7.95/1.51  ------ 
% 7.95/1.51  ------ Parsing...
% 7.95/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.95/1.51  
% 7.95/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.95/1.51  
% 7.95/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.95/1.51  
% 7.95/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.95/1.51  ------ Proving...
% 7.95/1.51  ------ Problem Properties 
% 7.95/1.51  
% 7.95/1.51  
% 7.95/1.51  clauses                                 38
% 7.95/1.51  conjectures                             13
% 7.95/1.51  EPR                                     10
% 7.95/1.51  Horn                                    29
% 7.95/1.51  unary                                   18
% 7.95/1.51  binary                                  6
% 7.95/1.51  lits                                    149
% 7.95/1.51  lits eq                                 22
% 7.95/1.51  fd_pure                                 0
% 7.95/1.51  fd_pseudo                               0
% 7.95/1.51  fd_cond                                 0
% 7.95/1.51  fd_pseudo_cond                          3
% 7.95/1.51  AC symbols                              0
% 7.95/1.51  
% 7.95/1.51  ------ Input Options Time Limit: Unbounded
% 7.95/1.51  
% 7.95/1.51  
% 7.95/1.51  ------ 
% 7.95/1.51  Current options:
% 7.95/1.51  ------ 
% 7.95/1.51  
% 7.95/1.51  
% 7.95/1.51  
% 7.95/1.51  
% 7.95/1.51  ------ Proving...
% 7.95/1.51  
% 7.95/1.51  
% 7.95/1.51  % SZS status Theorem for theBenchmark.p
% 7.95/1.51  
% 7.95/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.95/1.51  
% 7.95/1.51  fof(f9,axiom,(
% 7.95/1.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f75,plain,(
% 7.95/1.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.95/1.51    inference(cnf_transformation,[],[f9])).
% 7.95/1.51  
% 7.95/1.51  fof(f3,axiom,(
% 7.95/1.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f69,plain,(
% 7.95/1.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.95/1.51    inference(cnf_transformation,[],[f3])).
% 7.95/1.51  
% 7.95/1.51  fof(f20,conjecture,(
% 7.95/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f21,negated_conjecture,(
% 7.95/1.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.95/1.51    inference(negated_conjecture,[],[f20])).
% 7.95/1.51  
% 7.95/1.51  fof(f47,plain,(
% 7.95/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.95/1.51    inference(ennf_transformation,[],[f21])).
% 7.95/1.51  
% 7.95/1.51  fof(f48,plain,(
% 7.95/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.95/1.51    inference(flattening,[],[f47])).
% 7.95/1.51  
% 7.95/1.51  fof(f63,plain,(
% 7.95/1.51    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 7.95/1.51    introduced(choice_axiom,[])).
% 7.95/1.51  
% 7.95/1.51  fof(f62,plain,(
% 7.95/1.51    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 7.95/1.51    introduced(choice_axiom,[])).
% 7.95/1.51  
% 7.95/1.51  fof(f61,plain,(
% 7.95/1.51    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 7.95/1.51    introduced(choice_axiom,[])).
% 7.95/1.51  
% 7.95/1.51  fof(f60,plain,(
% 7.95/1.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.95/1.51    introduced(choice_axiom,[])).
% 7.95/1.51  
% 7.95/1.51  fof(f59,plain,(
% 7.95/1.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 7.95/1.51    introduced(choice_axiom,[])).
% 7.95/1.51  
% 7.95/1.51  fof(f58,plain,(
% 7.95/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 7.95/1.51    introduced(choice_axiom,[])).
% 7.95/1.51  
% 7.95/1.51  fof(f64,plain,(
% 7.95/1.51    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.95/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f48,f63,f62,f61,f60,f59,f58])).
% 7.95/1.51  
% 7.95/1.51  fof(f107,plain,(
% 7.95/1.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f15,axiom,(
% 7.95/1.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f37,plain,(
% 7.95/1.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.95/1.51    inference(ennf_transformation,[],[f15])).
% 7.95/1.51  
% 7.95/1.51  fof(f38,plain,(
% 7.95/1.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.95/1.51    inference(flattening,[],[f37])).
% 7.95/1.51  
% 7.95/1.51  fof(f85,plain,(
% 7.95/1.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f38])).
% 7.95/1.51  
% 7.95/1.51  fof(f14,axiom,(
% 7.95/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f23,plain,(
% 7.95/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.95/1.51    inference(pure_predicate_removal,[],[f14])).
% 7.95/1.51  
% 7.95/1.51  fof(f36,plain,(
% 7.95/1.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.95/1.51    inference(ennf_transformation,[],[f23])).
% 7.95/1.51  
% 7.95/1.51  fof(f83,plain,(
% 7.95/1.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.95/1.51    inference(cnf_transformation,[],[f36])).
% 7.95/1.51  
% 7.95/1.51  fof(f16,axiom,(
% 7.95/1.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f39,plain,(
% 7.95/1.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.95/1.51    inference(ennf_transformation,[],[f16])).
% 7.95/1.51  
% 7.95/1.51  fof(f40,plain,(
% 7.95/1.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.95/1.51    inference(flattening,[],[f39])).
% 7.95/1.51  
% 7.95/1.51  fof(f55,plain,(
% 7.95/1.51    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.95/1.51    inference(nnf_transformation,[],[f40])).
% 7.95/1.51  
% 7.95/1.51  fof(f86,plain,(
% 7.95/1.51    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f55])).
% 7.95/1.51  
% 7.95/1.51  fof(f13,axiom,(
% 7.95/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f35,plain,(
% 7.95/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.95/1.51    inference(ennf_transformation,[],[f13])).
% 7.95/1.51  
% 7.95/1.51  fof(f82,plain,(
% 7.95/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.95/1.51    inference(cnf_transformation,[],[f35])).
% 7.95/1.51  
% 7.95/1.51  fof(f96,plain,(
% 7.95/1.51    ~v1_xboole_0(sK3)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f105,plain,(
% 7.95/1.51    v1_funct_1(sK7)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f106,plain,(
% 7.95/1.51    v1_funct_2(sK7,sK5,sK3)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f12,axiom,(
% 7.95/1.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1)) => k7_relat_1(X2,X0) = X1)))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f33,plain,(
% 7.95/1.51    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.95/1.51    inference(ennf_transformation,[],[f12])).
% 7.95/1.51  
% 7.95/1.51  fof(f34,plain,(
% 7.95/1.51    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.95/1.51    inference(flattening,[],[f33])).
% 7.95/1.51  
% 7.95/1.51  fof(f53,plain,(
% 7.95/1.51    ! [X2,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK1(X1,X2)) != k1_funct_1(X2,sK1(X1,X2)) & r2_hidden(sK1(X1,X2),k1_relat_1(X1))))),
% 7.95/1.51    introduced(choice_axiom,[])).
% 7.95/1.51  
% 7.95/1.51  fof(f54,plain,(
% 7.95/1.51    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | (k1_funct_1(X1,sK1(X1,X2)) != k1_funct_1(X2,sK1(X1,X2)) & r2_hidden(sK1(X1,X2),k1_relat_1(X1))) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.95/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f53])).
% 7.95/1.51  
% 7.95/1.51  fof(f80,plain,(
% 7.95/1.51    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | r2_hidden(sK1(X1,X2),k1_relat_1(X1)) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f54])).
% 7.95/1.51  
% 7.95/1.51  fof(f6,axiom,(
% 7.95/1.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f72,plain,(
% 7.95/1.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.95/1.51    inference(cnf_transformation,[],[f6])).
% 7.95/1.51  
% 7.95/1.51  fof(f10,axiom,(
% 7.95/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f29,plain,(
% 7.95/1.51    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.95/1.51    inference(ennf_transformation,[],[f10])).
% 7.95/1.51  
% 7.95/1.51  fof(f30,plain,(
% 7.95/1.51    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.95/1.51    inference(flattening,[],[f29])).
% 7.95/1.51  
% 7.95/1.51  fof(f77,plain,(
% 7.95/1.51    ( ! [X0,X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f30])).
% 7.95/1.51  
% 7.95/1.51  fof(f4,axiom,(
% 7.95/1.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f70,plain,(
% 7.95/1.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f4])).
% 7.95/1.51  
% 7.95/1.51  fof(f2,axiom,(
% 7.95/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f22,plain,(
% 7.95/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.95/1.51    inference(rectify,[],[f2])).
% 7.95/1.51  
% 7.95/1.51  fof(f24,plain,(
% 7.95/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.95/1.51    inference(ennf_transformation,[],[f22])).
% 7.95/1.51  
% 7.95/1.51  fof(f50,plain,(
% 7.95/1.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.95/1.51    introduced(choice_axiom,[])).
% 7.95/1.51  
% 7.95/1.51  fof(f51,plain,(
% 7.95/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.95/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f50])).
% 7.95/1.51  
% 7.95/1.51  fof(f68,plain,(
% 7.95/1.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.95/1.51    inference(cnf_transformation,[],[f51])).
% 7.95/1.51  
% 7.95/1.51  fof(f11,axiom,(
% 7.95/1.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f31,plain,(
% 7.95/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.95/1.51    inference(ennf_transformation,[],[f11])).
% 7.95/1.51  
% 7.95/1.51  fof(f32,plain,(
% 7.95/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.95/1.51    inference(flattening,[],[f31])).
% 7.95/1.51  
% 7.95/1.51  fof(f52,plain,(
% 7.95/1.51    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.95/1.51    inference(nnf_transformation,[],[f32])).
% 7.95/1.51  
% 7.95/1.51  fof(f78,plain,(
% 7.95/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f52])).
% 7.95/1.51  
% 7.95/1.51  fof(f101,plain,(
% 7.95/1.51    r1_subset_1(sK4,sK5)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f97,plain,(
% 7.95/1.51    ~v1_xboole_0(sK4)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f99,plain,(
% 7.95/1.51    ~v1_xboole_0(sK5)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f1,axiom,(
% 7.95/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f49,plain,(
% 7.95/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.95/1.51    inference(nnf_transformation,[],[f1])).
% 7.95/1.51  
% 7.95/1.51  fof(f65,plain,(
% 7.95/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f49])).
% 7.95/1.51  
% 7.95/1.51  fof(f100,plain,(
% 7.95/1.51    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f5,axiom,(
% 7.95/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f25,plain,(
% 7.95/1.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.95/1.51    inference(ennf_transformation,[],[f5])).
% 7.95/1.51  
% 7.95/1.51  fof(f71,plain,(
% 7.95/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.95/1.51    inference(cnf_transformation,[],[f25])).
% 7.95/1.51  
% 7.95/1.51  fof(f104,plain,(
% 7.95/1.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f17,axiom,(
% 7.95/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f41,plain,(
% 7.95/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.95/1.51    inference(ennf_transformation,[],[f17])).
% 7.95/1.51  
% 7.95/1.51  fof(f42,plain,(
% 7.95/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.95/1.51    inference(flattening,[],[f41])).
% 7.95/1.51  
% 7.95/1.51  fof(f88,plain,(
% 7.95/1.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f42])).
% 7.95/1.51  
% 7.95/1.51  fof(f102,plain,(
% 7.95/1.51    v1_funct_1(sK6)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f108,plain,(
% 7.95/1.51    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f95,plain,(
% 7.95/1.51    ~v1_xboole_0(sK2)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f98,plain,(
% 7.95/1.51    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f103,plain,(
% 7.95/1.51    v1_funct_2(sK6,sK4,sK3)),
% 7.95/1.51    inference(cnf_transformation,[],[f64])).
% 7.95/1.51  
% 7.95/1.51  fof(f18,axiom,(
% 7.95/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f43,plain,(
% 7.95/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.95/1.51    inference(ennf_transformation,[],[f18])).
% 7.95/1.51  
% 7.95/1.51  fof(f44,plain,(
% 7.95/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.95/1.51    inference(flattening,[],[f43])).
% 7.95/1.51  
% 7.95/1.51  fof(f56,plain,(
% 7.95/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.95/1.51    inference(nnf_transformation,[],[f44])).
% 7.95/1.51  
% 7.95/1.51  fof(f57,plain,(
% 7.95/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.95/1.51    inference(flattening,[],[f56])).
% 7.95/1.51  
% 7.95/1.51  fof(f89,plain,(
% 7.95/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f57])).
% 7.95/1.51  
% 7.95/1.51  fof(f113,plain,(
% 7.95/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.95/1.51    inference(equality_resolution,[],[f89])).
% 7.95/1.51  
% 7.95/1.51  fof(f19,axiom,(
% 7.95/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.95/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.51  
% 7.95/1.51  fof(f45,plain,(
% 7.95/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.95/1.51    inference(ennf_transformation,[],[f19])).
% 7.95/1.51  
% 7.95/1.51  fof(f46,plain,(
% 7.95/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.95/1.51    inference(flattening,[],[f45])).
% 7.95/1.51  
% 7.95/1.51  fof(f92,plain,(
% 7.95/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f46])).
% 7.95/1.51  
% 7.95/1.51  fof(f93,plain,(
% 7.95/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f46])).
% 7.95/1.51  
% 7.95/1.51  fof(f94,plain,(
% 7.95/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f46])).
% 7.95/1.51  
% 7.95/1.51  fof(f90,plain,(
% 7.95/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.95/1.51    inference(cnf_transformation,[],[f57])).
% 7.95/1.51  
% 7.95/1.51  fof(f112,plain,(
% 7.95/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.95/1.51    inference(equality_resolution,[],[f90])).
% 7.95/1.51  
% 7.95/1.51  cnf(c_11,plain,
% 7.95/1.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.95/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4,plain,
% 7.95/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.95/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_31,negated_conjecture,
% 7.95/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.95/1.51      inference(cnf_transformation,[],[f107]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2169,plain,
% 7.95/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_19,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | v1_partfun1(X0,X1)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | v1_xboole_0(X2) ),
% 7.95/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_18,plain,
% 7.95/1.51      ( v4_relat_1(X0,X1)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.95/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_22,plain,
% 7.95/1.51      ( ~ v1_partfun1(X0,X1)
% 7.95/1.51      | ~ v4_relat_1(X0,X1)
% 7.95/1.51      | ~ v1_relat_1(X0)
% 7.95/1.51      | k1_relat_1(X0) = X1 ),
% 7.95/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_535,plain,
% 7.95/1.51      ( ~ v1_partfun1(X0,X1)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ v1_relat_1(X0)
% 7.95/1.51      | k1_relat_1(X0) = X1 ),
% 7.95/1.51      inference(resolution,[status(thm)],[c_18,c_22]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_17,plain,
% 7.95/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | v1_relat_1(X0) ),
% 7.95/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_539,plain,
% 7.95/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ v1_partfun1(X0,X1)
% 7.95/1.51      | k1_relat_1(X0) = X1 ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_535,c_22,c_18,c_17]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_540,plain,
% 7.95/1.51      ( ~ v1_partfun1(X0,X1)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | k1_relat_1(X0) = X1 ),
% 7.95/1.51      inference(renaming,[status(thm)],[c_539]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_593,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | k1_relat_1(X0) = X1 ),
% 7.95/1.51      inference(resolution,[status(thm)],[c_19,c_540]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_597,plain,
% 7.95/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | k1_relat_1(X0) = X1 ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_593,c_22,c_19,c_18,c_17]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_598,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | k1_relat_1(X0) = X1 ),
% 7.95/1.51      inference(renaming,[status(thm)],[c_597]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2154,plain,
% 7.95/1.51      ( k1_relat_1(X0) = X1
% 7.95/1.51      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.95/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.95/1.51      | v1_funct_1(X0) != iProver_top
% 7.95/1.51      | v1_xboole_0(X2) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3008,plain,
% 7.95/1.51      ( k1_relat_1(sK7) = sK5
% 7.95/1.51      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.95/1.51      | v1_funct_1(sK7) != iProver_top
% 7.95/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_2169,c_2154]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_42,negated_conjecture,
% 7.95/1.51      ( ~ v1_xboole_0(sK3) ),
% 7.95/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_33,negated_conjecture,
% 7.95/1.51      ( v1_funct_1(sK7) ),
% 7.95/1.51      inference(cnf_transformation,[],[f105]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_32,negated_conjecture,
% 7.95/1.51      ( v1_funct_2(sK7,sK5,sK3) ),
% 7.95/1.51      inference(cnf_transformation,[],[f106]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2433,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,X0,X1)
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | k1_relat_1(sK7) = X0 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_598]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2664,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,sK5,sK3)
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | v1_xboole_0(sK3)
% 7.95/1.51      | k1_relat_1(sK7) = sK5 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2433]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_6618,plain,
% 7.95/1.51      ( k1_relat_1(sK7) = sK5 ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_3008,c_42,c_33,c_32,c_31,c_2664]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_16,plain,
% 7.95/1.51      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 7.95/1.51      | ~ v1_relat_1(X0)
% 7.95/1.51      | ~ v1_relat_1(X1)
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(X1)
% 7.95/1.51      | k7_relat_1(X1,X2) = X0
% 7.95/1.51      | k3_xboole_0(k1_relat_1(X1),X2) != k1_relat_1(X0) ),
% 7.95/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2176,plain,
% 7.95/1.51      ( k7_relat_1(X0,X1) = X2
% 7.95/1.51      | k3_xboole_0(k1_relat_1(X0),X1) != k1_relat_1(X2)
% 7.95/1.51      | r2_hidden(sK1(X2,X0),k1_relat_1(X2)) = iProver_top
% 7.95/1.51      | v1_relat_1(X2) != iProver_top
% 7.95/1.51      | v1_relat_1(X0) != iProver_top
% 7.95/1.51      | v1_funct_1(X2) != iProver_top
% 7.95/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_6622,plain,
% 7.95/1.51      ( k7_relat_1(sK7,X0) = X1
% 7.95/1.51      | k3_xboole_0(sK5,X0) != k1_relat_1(X1)
% 7.95/1.51      | r2_hidden(sK1(X1,sK7),k1_relat_1(X1)) = iProver_top
% 7.95/1.51      | v1_relat_1(X1) != iProver_top
% 7.95/1.51      | v1_relat_1(sK7) != iProver_top
% 7.95/1.51      | v1_funct_1(X1) != iProver_top
% 7.95/1.51      | v1_funct_1(sK7) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_6618,c_2176]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_54,plain,
% 7.95/1.51      ( v1_funct_1(sK7) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_56,plain,
% 7.95/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2313,plain,
% 7.95/1.51      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.95/1.51      | v1_relat_1(sK7) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2314,plain,
% 7.95/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.95/1.51      | v1_relat_1(sK7) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_2313]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_9084,plain,
% 7.95/1.51      ( v1_funct_1(X1) != iProver_top
% 7.95/1.51      | k7_relat_1(sK7,X0) = X1
% 7.95/1.51      | k3_xboole_0(sK5,X0) != k1_relat_1(X1)
% 7.95/1.51      | r2_hidden(sK1(X1,sK7),k1_relat_1(X1)) = iProver_top
% 7.95/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_6622,c_54,c_56,c_2314]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_9085,plain,
% 7.95/1.51      ( k7_relat_1(sK7,X0) = X1
% 7.95/1.51      | k3_xboole_0(sK5,X0) != k1_relat_1(X1)
% 7.95/1.51      | r2_hidden(sK1(X1,sK7),k1_relat_1(X1)) = iProver_top
% 7.95/1.51      | v1_relat_1(X1) != iProver_top
% 7.95/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.95/1.51      inference(renaming,[status(thm)],[c_9084]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_9090,plain,
% 7.95/1.51      ( k7_relat_1(sK7,k1_xboole_0) = X0
% 7.95/1.51      | k1_relat_1(X0) != k1_xboole_0
% 7.95/1.51      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 7.95/1.51      | v1_relat_1(X0) != iProver_top
% 7.95/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_4,c_9085]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_9095,plain,
% 7.95/1.51      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0
% 7.95/1.51      | r2_hidden(sK1(k1_xboole_0,sK7),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.95/1.51      | v1_relat_1(k1_xboole_0) != iProver_top
% 7.95/1.51      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_11,c_9090]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2175,plain,
% 7.95/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.95/1.51      | v1_relat_1(X0) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3147,plain,
% 7.95/1.51      ( v1_relat_1(sK7) = iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_2169,c_2175]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3787,plain,
% 7.95/1.51      ( k7_relat_1(X0,k1_xboole_0) = X1
% 7.95/1.51      | k1_relat_1(X1) != k1_xboole_0
% 7.95/1.51      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 7.95/1.51      | v1_relat_1(X1) != iProver_top
% 7.95/1.51      | v1_relat_1(X0) != iProver_top
% 7.95/1.51      | v1_funct_1(X1) != iProver_top
% 7.95/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_4,c_2176]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3796,plain,
% 7.95/1.51      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.95/1.51      | r2_hidden(sK1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.95/1.51      | v1_relat_1(X0) != iProver_top
% 7.95/1.51      | v1_relat_1(k1_xboole_0) != iProver_top
% 7.95/1.51      | v1_funct_1(X0) != iProver_top
% 7.95/1.51      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_11,c_3787]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2303,plain,
% 7.95/1.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.95/1.51      | v1_relat_1(k1_xboole_0) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2305,plain,
% 7.95/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.95/1.51      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_2303]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_7,plain,
% 7.95/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.95/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2304,plain,
% 7.95/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2309,plain,
% 7.95/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_2304]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_12,plain,
% 7.95/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.95/1.51      | ~ v1_relat_1(X1)
% 7.95/1.51      | ~ v1_funct_1(X1)
% 7.95/1.51      | v1_funct_1(X0) ),
% 7.95/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2531,plain,
% 7.95/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
% 7.95/1.51      | ~ v1_relat_1(sK7)
% 7.95/1.51      | v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(sK7) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2878,plain,
% 7.95/1.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK7))
% 7.95/1.51      | ~ v1_relat_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | v1_funct_1(k1_xboole_0) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2531]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2880,plain,
% 7.95/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK7)) != iProver_top
% 7.95/1.51      | v1_relat_1(sK7) != iProver_top
% 7.95/1.51      | v1_funct_1(sK7) != iProver_top
% 7.95/1.51      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_2878]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2879,plain,
% 7.95/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK7)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2882,plain,
% 7.95/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK7)) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_2879]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4055,plain,
% 7.95/1.51      ( v1_funct_1(X0) != iProver_top
% 7.95/1.51      | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.95/1.51      | r2_hidden(sK1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.95/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_3796,c_54,c_56,c_2305,c_2309,c_2314,c_2880,c_2882]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4056,plain,
% 7.95/1.51      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.95/1.51      | r2_hidden(sK1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.95/1.51      | v1_relat_1(X0) != iProver_top
% 7.95/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.95/1.51      inference(renaming,[status(thm)],[c_4055]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4061,plain,
% 7.95/1.51      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.95/1.51      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 7.95/1.51      | v1_relat_1(X0) != iProver_top
% 7.95/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_11,c_4056]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_5,plain,
% 7.95/1.51      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.95/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2183,plain,
% 7.95/1.51      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2,plain,
% 7.95/1.51      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.95/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2185,plain,
% 7.95/1.51      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 7.95/1.51      | r1_xboole_0(X1,X2) != iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3239,plain,
% 7.95/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.95/1.51      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_4,c_2185]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3334,plain,
% 7.95/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_2183,c_3239]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4977,plain,
% 7.95/1.51      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.95/1.51      | v1_relat_1(X0) != iProver_top
% 7.95/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_4061,c_3334]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_7872,plain,
% 7.95/1.51      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0
% 7.95/1.51      | v1_funct_1(sK7) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_3147,c_4977]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_9729,plain,
% 7.95/1.51      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_9095,c_54,c_7872]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_14,plain,
% 7.95/1.51      ( ~ r1_subset_1(X0,X1)
% 7.95/1.51      | r1_xboole_0(X0,X1)
% 7.95/1.51      | v1_xboole_0(X0)
% 7.95/1.51      | v1_xboole_0(X1) ),
% 7.95/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_37,negated_conjecture,
% 7.95/1.51      ( r1_subset_1(sK4,sK5) ),
% 7.95/1.51      inference(cnf_transformation,[],[f101]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_580,plain,
% 7.95/1.51      ( r1_xboole_0(X0,X1)
% 7.95/1.51      | v1_xboole_0(X0)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | sK5 != X1
% 7.95/1.51      | sK4 != X0 ),
% 7.95/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_37]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_581,plain,
% 7.95/1.51      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 7.95/1.51      inference(unflattening,[status(thm)],[c_580]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_41,negated_conjecture,
% 7.95/1.51      ( ~ v1_xboole_0(sK4) ),
% 7.95/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_39,negated_conjecture,
% 7.95/1.51      ( ~ v1_xboole_0(sK5) ),
% 7.95/1.51      inference(cnf_transformation,[],[f99]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_583,plain,
% 7.95/1.51      ( r1_xboole_0(sK4,sK5) ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_581,c_41,c_39]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2155,plain,
% 7.95/1.51      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_1,plain,
% 7.95/1.51      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.95/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2186,plain,
% 7.95/1.51      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 7.95/1.51      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3102,plain,
% 7.95/1.51      ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_2155,c_2186]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_38,negated_conjecture,
% 7.95/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.95/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2163,plain,
% 7.95/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_6,plain,
% 7.95/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.95/1.51      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.95/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2182,plain,
% 7.95/1.51      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 7.95/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3342,plain,
% 7.95/1.51      ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_2163,c_2182]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_34,negated_conjecture,
% 7.95/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.95/1.51      inference(cnf_transformation,[],[f104]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2166,plain,
% 7.95/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_23,plain,
% 7.95/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.95/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2174,plain,
% 7.95/1.51      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.95/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.95/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3646,plain,
% 7.95/1.51      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
% 7.95/1.51      | v1_funct_1(sK6) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_2166,c_2174]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_36,negated_conjecture,
% 7.95/1.51      ( v1_funct_1(sK6) ),
% 7.95/1.51      inference(cnf_transformation,[],[f102]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2428,plain,
% 7.95/1.51      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2659,plain,
% 7.95/1.51      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2428]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_7374,plain,
% 7.95/1.51      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_3646,c_36,c_34,c_2659]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3645,plain,
% 7.95/1.51      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
% 7.95/1.51      | v1_funct_1(sK7) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_2169,c_2174]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2423,plain,
% 7.95/1.51      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | k2_partfun1(X0,X1,sK7,X2) = k7_relat_1(sK7,X2) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2654,plain,
% 7.95/1.51      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2423]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_7269,plain,
% 7.95/1.51      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_3645,c_33,c_31,c_2654]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_30,negated_conjecture,
% 7.95/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.95/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(cnf_transformation,[],[f108]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_7272,plain,
% 7.95/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.95/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_7269,c_30]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_43,negated_conjecture,
% 7.95/1.51      ( ~ v1_xboole_0(sK2) ),
% 7.95/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_40,negated_conjecture,
% 7.95/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 7.95/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_35,negated_conjecture,
% 7.95/1.51      ( v1_funct_2(sK6,sK4,sK3) ),
% 7.95/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_1282,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2345,plain,
% 7.95/1.51      ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != X0
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != X0
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_1282]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2583,plain,
% 7.95/1.51      ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2345]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_1281,plain,( X0 = X0 ),theory(equality) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2584,plain,
% 7.95/1.51      ( k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_1281]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2870,plain,
% 7.95/1.51      ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != X0
% 7.95/1.51      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != X0 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_1282]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4096,plain,
% 7.95/1.51      ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
% 7.95/1.51      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5))
% 7.95/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2870]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4097,plain,
% 7.95/1.51      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2654]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_26,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(X3)
% 7.95/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.95/1.51      inference(cnf_transformation,[],[f113]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_29,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(X3)
% 7.95/1.51      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X1) ),
% 7.95/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_28,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(X3)
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X1) ),
% 7.95/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_27,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(X3)
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X1) ),
% 7.95/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_228,plain,
% 7.95/1.51      ( ~ v1_funct_1(X3)
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_26,c_29,c_28,c_27]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_229,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(X3)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.95/1.51      inference(renaming,[status(thm)],[c_228]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2514,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(sK6,X3,X2)
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X3)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK6,k9_subset_1(X4,X3,X1))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK6,X0),X3) = sK6 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_229]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2806,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,X0,X1)
% 7.95/1.51      | ~ v1_funct_2(sK6,X2,X1)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 7.95/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(X0)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X3)
% 7.95/1.51      | k2_partfun1(X0,X1,sK7,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK6,k9_subset_1(X3,X2,X0))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK6,sK7),X2) = sK6 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2514]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3308,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,X0,sK3)
% 7.95/1.51      | ~ v1_funct_2(sK6,sK4,sK3)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(X1))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(X0)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | v1_xboole_0(sK3)
% 7.95/1.51      | v1_xboole_0(sK4)
% 7.95/1.51      | k2_partfun1(X0,sK3,sK7,k9_subset_1(X1,sK4,X0)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X1,sK4,X0))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X1,sK4,X0),sK3,k1_tmap_1(X1,sK3,sK4,X0,sK6,sK7),sK4) = sK6 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2806]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3604,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,sK5,sK3)
% 7.95/1.51      | ~ v1_funct_2(sK6,sK4,sK3)
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 7.95/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(X0)
% 7.95/1.51      | v1_xboole_0(sK3)
% 7.95/1.51      | v1_xboole_0(sK5)
% 7.95/1.51      | v1_xboole_0(sK4)
% 7.95/1.51      | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.95/1.51      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(X0,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X0,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_3308]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4915,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,sK5,sK3)
% 7.95/1.51      | ~ v1_funct_2(sK6,sK4,sK3)
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 7.95/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(sK3)
% 7.95/1.51      | v1_xboole_0(sK5)
% 7.95/1.51      | v1_xboole_0(sK4)
% 7.95/1.51      | v1_xboole_0(sK2)
% 7.95/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.95/1.51      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_3604]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_25,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(X3)
% 7.95/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.95/1.51      inference(cnf_transformation,[],[f112]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_235,plain,
% 7.95/1.51      ( ~ v1_funct_1(X3)
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_25,c_29,c_28,c_27]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_236,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.95/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(X3)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | v1_xboole_0(X5)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.95/1.51      inference(renaming,[status(thm)],[c_235]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2524,plain,
% 7.95/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.95/1.51      | ~ v1_funct_2(sK6,X3,X2)
% 7.95/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 7.95/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.95/1.51      | ~ v1_funct_1(X0)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X3)
% 7.95/1.51      | v1_xboole_0(X4)
% 7.95/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK6,k9_subset_1(X4,X3,X1))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK6,X0),X1) = X0 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_236]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_2824,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,X0,X1)
% 7.95/1.51      | ~ v1_funct_2(sK6,X2,X1)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 7.95/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(X0)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | v1_xboole_0(X2)
% 7.95/1.51      | v1_xboole_0(X3)
% 7.95/1.51      | k2_partfun1(X0,X1,sK7,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK6,k9_subset_1(X3,X2,X0))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK6,sK7),X0) = sK7 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2524]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3328,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,X0,sK3)
% 7.95/1.51      | ~ v1_funct_2(sK6,sK4,sK3)
% 7.95/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(X1))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(X0)
% 7.95/1.51      | v1_xboole_0(X1)
% 7.95/1.51      | v1_xboole_0(sK3)
% 7.95/1.51      | v1_xboole_0(sK4)
% 7.95/1.51      | k2_partfun1(X0,sK3,sK7,k9_subset_1(X1,sK4,X0)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X1,sK4,X0))
% 7.95/1.51      | k2_partfun1(k4_subset_1(X1,sK4,X0),sK3,k1_tmap_1(X1,sK3,sK4,X0,sK6,sK7),X0) = sK7 ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_2824]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3626,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,sK5,sK3)
% 7.95/1.51      | ~ v1_funct_2(sK6,sK4,sK3)
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 7.95/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(X0)
% 7.95/1.51      | v1_xboole_0(sK3)
% 7.95/1.51      | v1_xboole_0(sK5)
% 7.95/1.51      | v1_xboole_0(sK4)
% 7.95/1.51      | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.95/1.51      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(X0,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X0,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_3328]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_4927,plain,
% 7.95/1.51      ( ~ v1_funct_2(sK7,sK5,sK3)
% 7.95/1.51      | ~ v1_funct_2(sK6,sK4,sK3)
% 7.95/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.95/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 7.95/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 7.95/1.51      | ~ v1_funct_1(sK7)
% 7.95/1.51      | ~ v1_funct_1(sK6)
% 7.95/1.51      | v1_xboole_0(sK3)
% 7.95/1.51      | v1_xboole_0(sK5)
% 7.95/1.51      | v1_xboole_0(sK4)
% 7.95/1.51      | v1_xboole_0(sK2)
% 7.95/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.95/1.51      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(instantiation,[status(thm)],[c_3626]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_7370,plain,
% 7.95/1.51      ( k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(global_propositional_subsumption,
% 7.95/1.51                [status(thm)],
% 7.95/1.51                [c_7272,c_43,c_42,c_41,c_40,c_39,c_38,c_36,c_35,c_34,
% 7.95/1.51                 c_33,c_32,c_31,c_30,c_2583,c_2584,c_4096,c_4097,c_4915,
% 7.95/1.51                 c_4927]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_7377,plain,
% 7.95/1.51      ( k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_7374,c_7370]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_19879,plain,
% 7.95/1.51      ( k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_3342,c_7377]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_20159,plain,
% 7.95/1.51      ( k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_3342,c_19879]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_20160,plain,
% 7.95/1.51      ( k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_3102,c_20159]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_20233,plain,
% 7.95/1.51      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_3102,c_20160]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_20449,plain,
% 7.95/1.51      ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_9729,c_20233]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_3148,plain,
% 7.95/1.51      ( v1_relat_1(sK6) = iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_2166,c_2175]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_7873,plain,
% 7.95/1.51      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0
% 7.95/1.51      | v1_funct_1(sK6) != iProver_top ),
% 7.95/1.51      inference(superposition,[status(thm)],[c_3148,c_4977]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(c_51,plain,
% 7.95/1.51      ( v1_funct_1(sK6) = iProver_top ),
% 7.95/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.95/1.51  
% 7.95/1.51  cnf(contradiction,plain,
% 7.95/1.51      ( $false ),
% 7.95/1.51      inference(minisat,[status(thm)],[c_20449,c_7873,c_51]) ).
% 7.95/1.51  
% 7.95/1.51  
% 7.95/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.95/1.51  
% 7.95/1.51  ------                               Statistics
% 7.95/1.51  
% 7.95/1.51  ------ Selected
% 7.95/1.51  
% 7.95/1.51  total_time:                             0.817
% 7.95/1.51  
%------------------------------------------------------------------------------
