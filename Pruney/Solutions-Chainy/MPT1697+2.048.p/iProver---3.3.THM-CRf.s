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
% DateTime   : Thu Dec  3 12:21:32 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  185 (1375 expanded)
%              Number of clauses        :  117 ( 358 expanded)
%              Number of leaves         :   17 ( 525 expanded)
%              Depth                    :   23
%              Number of atoms          : 1048 (16902 expanded)
%              Number of equality atoms :  384 (4027 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f38,f56,f55,f54,f53,f52,f51])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f94,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f15,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f98,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1433,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_2313,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1433])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1449,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2298,plain,
    ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_3279,plain,
    ( k9_subset_1(sK2,X0_57,sK5) = k1_setfam_1(k2_tarski(X0_57,sK5)) ),
    inference(superposition,[status(thm)],[c_2313,c_2298])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1436,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2310,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1436])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2302,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1445])).

cnf(c_3665,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2310,c_2302])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2764,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0_57,X1_57,sK6,X2_57) = k7_relat_1(sK6,X2_57) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_2959,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_3875,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3665,c_32,c_30,c_2959])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1439,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2307,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1439])).

cnf(c_3664,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_2302])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2759,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0_57,X1_57,sK7,X2_57) = k7_relat_1(sK7,X2_57) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_2954,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
    inference(instantiation,[status(thm)],[c_2759])).

cnf(c_3869,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3664,c_29,c_27,c_2954])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f105])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f84])).

cnf(c_225,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_25,c_24,c_23])).

cnf(c_226,plain,
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
    inference(renaming,[status(thm)],[c_225])).

cnf(c_1426,plain,
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
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_2320,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
    | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
    | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
    | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_funct_1(X5_57) != iProver_top
    | v1_xboole_0(X3_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1426])).

cnf(c_7144,plain,
    ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3869,c_2320])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_44,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_50,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_51,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_52,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9593,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
    | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7144,c_41,c_44,c_50,c_51,c_52])).

cnf(c_9594,plain,
    ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_9593])).

cnf(c_9609,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3875,c_9594])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_42,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_48,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_49,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9792,plain,
    ( v1_xboole_0(X0_57) = iProver_top
    | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9609,c_42,c_47,c_48,c_49])).

cnf(c_9793,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_9792])).

cnf(c_9803,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_9793])).

cnf(c_12,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_592,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_593,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_595,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_37,c_35])).

cnf(c_1425,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_595])).

cnf(c_2321,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1454,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2293,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1454])).

cnf(c_3231,plain,
    ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2321,c_2293])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1446,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2301,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1446])).

cnf(c_3346,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_2301])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1450,plain,
    ( r1_xboole_0(X0_57,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2297,plain,
    ( r1_xboole_0(X0_57,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1448,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2299,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_3408,plain,
    ( k7_relat_1(X0_57,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_2297,c_2299])).

cnf(c_6324,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3346,c_3408])).

cnf(c_9804,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9803,c_3231,c_6324])).

cnf(c_9805,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9804,c_3279])).

cnf(c_3347,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2310,c_2301])).

cnf(c_6325,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3347,c_3408])).

cnf(c_9806,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9805,c_3231,c_6325])).

cnf(c_9807,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9806])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f106])).

cnf(c_218,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_25,c_24,c_23])).

cnf(c_219,plain,
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
    inference(renaming,[status(thm)],[c_218])).

cnf(c_1427,plain,
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
    inference(subtyping,[status(esa)],[c_219])).

cnf(c_2319,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
    | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
    | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
    | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_funct_1(X5_57) != iProver_top
    | v1_xboole_0(X3_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_5933,plain,
    ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3869,c_2319])).

cnf(c_6512,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
    | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5933,c_41,c_44,c_50,c_51,c_52])).

cnf(c_6513,plain,
    ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_6512])).

cnf(c_6528,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3875,c_6513])).

cnf(c_6739,plain,
    ( v1_xboole_0(X0_57) = iProver_top
    | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6528,c_42,c_47,c_48,c_49])).

cnf(c_6740,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_6739])).

cnf(c_6750,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_6740])).

cnf(c_6751,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6750,c_3231,c_6324])).

cnf(c_6752,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6751,c_3279])).

cnf(c_6753,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6752,c_3231,c_6325])).

cnf(c_6754,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6753])).

cnf(c_26,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1440,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3449,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(demodulation,[status(thm)],[c_3279,c_1440])).

cnf(c_3450,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3449,c_3231])).

cnf(c_3873,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3869,c_3450])).

cnf(c_3976,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3873,c_3875])).

cnf(c_6422,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6324,c_3976])).

cnf(c_3193,plain,
    ( r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_2886,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK6),X0_57)
    | ~ v1_relat_1(sK6)
    | k7_relat_1(sK6,X0_57) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_3192,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK6),k1_xboole_0)
    | ~ v1_relat_1(sK6)
    | k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2886])).

cnf(c_2675,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9807,c_6754,c_6422,c_3193,c_3192,c_2675,c_30,c_45,c_43,c_40])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.06/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/1.50  
% 7.06/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.06/1.50  
% 7.06/1.50  ------  iProver source info
% 7.06/1.50  
% 7.06/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.06/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.06/1.50  git: non_committed_changes: false
% 7.06/1.50  git: last_make_outside_of_git: false
% 7.06/1.50  
% 7.06/1.50  ------ 
% 7.06/1.50  
% 7.06/1.50  ------ Input Options
% 7.06/1.50  
% 7.06/1.50  --out_options                           all
% 7.06/1.50  --tptp_safe_out                         true
% 7.06/1.50  --problem_path                          ""
% 7.06/1.50  --include_path                          ""
% 7.06/1.50  --clausifier                            res/vclausify_rel
% 7.06/1.50  --clausifier_options                    --mode clausify
% 7.06/1.50  --stdin                                 false
% 7.06/1.50  --stats_out                             all
% 7.06/1.50  
% 7.06/1.50  ------ General Options
% 7.06/1.50  
% 7.06/1.50  --fof                                   false
% 7.06/1.50  --time_out_real                         305.
% 7.06/1.50  --time_out_virtual                      -1.
% 7.06/1.50  --symbol_type_check                     false
% 7.06/1.50  --clausify_out                          false
% 7.06/1.50  --sig_cnt_out                           false
% 7.06/1.50  --trig_cnt_out                          false
% 7.06/1.50  --trig_cnt_out_tolerance                1.
% 7.06/1.50  --trig_cnt_out_sk_spl                   false
% 7.06/1.50  --abstr_cl_out                          false
% 7.06/1.50  
% 7.06/1.50  ------ Global Options
% 7.06/1.50  
% 7.06/1.50  --schedule                              default
% 7.06/1.50  --add_important_lit                     false
% 7.06/1.50  --prop_solver_per_cl                    1000
% 7.06/1.50  --min_unsat_core                        false
% 7.06/1.50  --soft_assumptions                      false
% 7.06/1.50  --soft_lemma_size                       3
% 7.06/1.50  --prop_impl_unit_size                   0
% 7.06/1.50  --prop_impl_unit                        []
% 7.06/1.50  --share_sel_clauses                     true
% 7.06/1.50  --reset_solvers                         false
% 7.06/1.50  --bc_imp_inh                            [conj_cone]
% 7.06/1.50  --conj_cone_tolerance                   3.
% 7.06/1.50  --extra_neg_conj                        none
% 7.06/1.50  --large_theory_mode                     true
% 7.06/1.50  --prolific_symb_bound                   200
% 7.06/1.50  --lt_threshold                          2000
% 7.06/1.50  --clause_weak_htbl                      true
% 7.06/1.50  --gc_record_bc_elim                     false
% 7.06/1.50  
% 7.06/1.50  ------ Preprocessing Options
% 7.06/1.50  
% 7.06/1.50  --preprocessing_flag                    true
% 7.06/1.50  --time_out_prep_mult                    0.1
% 7.06/1.50  --splitting_mode                        input
% 7.06/1.50  --splitting_grd                         true
% 7.06/1.50  --splitting_cvd                         false
% 7.06/1.50  --splitting_cvd_svl                     false
% 7.06/1.50  --splitting_nvd                         32
% 7.06/1.50  --sub_typing                            true
% 7.06/1.50  --prep_gs_sim                           true
% 7.06/1.50  --prep_unflatten                        true
% 7.06/1.50  --prep_res_sim                          true
% 7.06/1.50  --prep_upred                            true
% 7.06/1.50  --prep_sem_filter                       exhaustive
% 7.06/1.50  --prep_sem_filter_out                   false
% 7.06/1.50  --pred_elim                             true
% 7.06/1.50  --res_sim_input                         true
% 7.06/1.50  --eq_ax_congr_red                       true
% 7.06/1.50  --pure_diseq_elim                       true
% 7.06/1.50  --brand_transform                       false
% 7.06/1.50  --non_eq_to_eq                          false
% 7.06/1.50  --prep_def_merge                        true
% 7.06/1.50  --prep_def_merge_prop_impl              false
% 7.06/1.50  --prep_def_merge_mbd                    true
% 7.06/1.50  --prep_def_merge_tr_red                 false
% 7.06/1.50  --prep_def_merge_tr_cl                  false
% 7.06/1.50  --smt_preprocessing                     true
% 7.06/1.50  --smt_ac_axioms                         fast
% 7.06/1.50  --preprocessed_out                      false
% 7.06/1.50  --preprocessed_stats                    false
% 7.06/1.50  
% 7.06/1.50  ------ Abstraction refinement Options
% 7.06/1.50  
% 7.06/1.50  --abstr_ref                             []
% 7.06/1.50  --abstr_ref_prep                        false
% 7.06/1.50  --abstr_ref_until_sat                   false
% 7.06/1.50  --abstr_ref_sig_restrict                funpre
% 7.06/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.50  --abstr_ref_under                       []
% 7.06/1.50  
% 7.06/1.50  ------ SAT Options
% 7.06/1.50  
% 7.06/1.50  --sat_mode                              false
% 7.06/1.50  --sat_fm_restart_options                ""
% 7.06/1.50  --sat_gr_def                            false
% 7.06/1.50  --sat_epr_types                         true
% 7.06/1.50  --sat_non_cyclic_types                  false
% 7.06/1.50  --sat_finite_models                     false
% 7.06/1.50  --sat_fm_lemmas                         false
% 7.06/1.50  --sat_fm_prep                           false
% 7.06/1.50  --sat_fm_uc_incr                        true
% 7.06/1.50  --sat_out_model                         small
% 7.06/1.50  --sat_out_clauses                       false
% 7.06/1.50  
% 7.06/1.50  ------ QBF Options
% 7.06/1.50  
% 7.06/1.50  --qbf_mode                              false
% 7.06/1.50  --qbf_elim_univ                         false
% 7.06/1.50  --qbf_dom_inst                          none
% 7.06/1.50  --qbf_dom_pre_inst                      false
% 7.06/1.50  --qbf_sk_in                             false
% 7.06/1.50  --qbf_pred_elim                         true
% 7.06/1.50  --qbf_split                             512
% 7.06/1.50  
% 7.06/1.50  ------ BMC1 Options
% 7.06/1.50  
% 7.06/1.50  --bmc1_incremental                      false
% 7.06/1.50  --bmc1_axioms                           reachable_all
% 7.06/1.50  --bmc1_min_bound                        0
% 7.06/1.50  --bmc1_max_bound                        -1
% 7.06/1.50  --bmc1_max_bound_default                -1
% 7.06/1.50  --bmc1_symbol_reachability              true
% 7.06/1.50  --bmc1_property_lemmas                  false
% 7.06/1.50  --bmc1_k_induction                      false
% 7.06/1.50  --bmc1_non_equiv_states                 false
% 7.06/1.50  --bmc1_deadlock                         false
% 7.06/1.50  --bmc1_ucm                              false
% 7.06/1.50  --bmc1_add_unsat_core                   none
% 7.06/1.50  --bmc1_unsat_core_children              false
% 7.06/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.50  --bmc1_out_stat                         full
% 7.06/1.50  --bmc1_ground_init                      false
% 7.06/1.50  --bmc1_pre_inst_next_state              false
% 7.06/1.50  --bmc1_pre_inst_state                   false
% 7.06/1.50  --bmc1_pre_inst_reach_state             false
% 7.06/1.50  --bmc1_out_unsat_core                   false
% 7.06/1.50  --bmc1_aig_witness_out                  false
% 7.06/1.50  --bmc1_verbose                          false
% 7.06/1.50  --bmc1_dump_clauses_tptp                false
% 7.06/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.50  --bmc1_dump_file                        -
% 7.06/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.50  --bmc1_ucm_extend_mode                  1
% 7.06/1.50  --bmc1_ucm_init_mode                    2
% 7.06/1.50  --bmc1_ucm_cone_mode                    none
% 7.06/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.50  --bmc1_ucm_relax_model                  4
% 7.06/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.50  --bmc1_ucm_layered_model                none
% 7.06/1.50  --bmc1_ucm_max_lemma_size               10
% 7.06/1.50  
% 7.06/1.50  ------ AIG Options
% 7.06/1.50  
% 7.06/1.50  --aig_mode                              false
% 7.06/1.50  
% 7.06/1.50  ------ Instantiation Options
% 7.06/1.50  
% 7.06/1.50  --instantiation_flag                    true
% 7.06/1.50  --inst_sos_flag                         false
% 7.06/1.50  --inst_sos_phase                        true
% 7.06/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.50  --inst_lit_sel_side                     num_symb
% 7.06/1.50  --inst_solver_per_active                1400
% 7.06/1.50  --inst_solver_calls_frac                1.
% 7.06/1.50  --inst_passive_queue_type               priority_queues
% 7.06/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.50  --inst_passive_queues_freq              [25;2]
% 7.06/1.50  --inst_dismatching                      true
% 7.06/1.50  --inst_eager_unprocessed_to_passive     true
% 7.06/1.50  --inst_prop_sim_given                   true
% 7.06/1.50  --inst_prop_sim_new                     false
% 7.06/1.50  --inst_subs_new                         false
% 7.06/1.50  --inst_eq_res_simp                      false
% 7.06/1.50  --inst_subs_given                       false
% 7.06/1.50  --inst_orphan_elimination               true
% 7.06/1.50  --inst_learning_loop_flag               true
% 7.06/1.50  --inst_learning_start                   3000
% 7.06/1.50  --inst_learning_factor                  2
% 7.06/1.50  --inst_start_prop_sim_after_learn       3
% 7.06/1.50  --inst_sel_renew                        solver
% 7.06/1.50  --inst_lit_activity_flag                true
% 7.06/1.50  --inst_restr_to_given                   false
% 7.06/1.50  --inst_activity_threshold               500
% 7.06/1.50  --inst_out_proof                        true
% 7.06/1.50  
% 7.06/1.50  ------ Resolution Options
% 7.06/1.50  
% 7.06/1.50  --resolution_flag                       true
% 7.06/1.50  --res_lit_sel                           adaptive
% 7.06/1.50  --res_lit_sel_side                      none
% 7.06/1.50  --res_ordering                          kbo
% 7.06/1.50  --res_to_prop_solver                    active
% 7.06/1.50  --res_prop_simpl_new                    false
% 7.06/1.50  --res_prop_simpl_given                  true
% 7.06/1.50  --res_passive_queue_type                priority_queues
% 7.06/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.50  --res_passive_queues_freq               [15;5]
% 7.06/1.50  --res_forward_subs                      full
% 7.06/1.50  --res_backward_subs                     full
% 7.06/1.50  --res_forward_subs_resolution           true
% 7.06/1.50  --res_backward_subs_resolution          true
% 7.06/1.50  --res_orphan_elimination                true
% 7.06/1.50  --res_time_limit                        2.
% 7.06/1.50  --res_out_proof                         true
% 7.06/1.50  
% 7.06/1.50  ------ Superposition Options
% 7.06/1.50  
% 7.06/1.50  --superposition_flag                    true
% 7.06/1.50  --sup_passive_queue_type                priority_queues
% 7.06/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.50  --demod_completeness_check              fast
% 7.06/1.50  --demod_use_ground                      true
% 7.06/1.50  --sup_to_prop_solver                    passive
% 7.06/1.50  --sup_prop_simpl_new                    true
% 7.06/1.50  --sup_prop_simpl_given                  true
% 7.06/1.50  --sup_fun_splitting                     false
% 7.06/1.50  --sup_smt_interval                      50000
% 7.06/1.50  
% 7.06/1.50  ------ Superposition Simplification Setup
% 7.06/1.50  
% 7.06/1.50  --sup_indices_passive                   []
% 7.06/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.50  --sup_full_bw                           [BwDemod]
% 7.06/1.50  --sup_immed_triv                        [TrivRules]
% 7.06/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.50  --sup_immed_bw_main                     []
% 7.06/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.50  
% 7.06/1.50  ------ Combination Options
% 7.06/1.50  
% 7.06/1.50  --comb_res_mult                         3
% 7.06/1.50  --comb_sup_mult                         2
% 7.06/1.50  --comb_inst_mult                        10
% 7.06/1.50  
% 7.06/1.50  ------ Debug Options
% 7.06/1.50  
% 7.06/1.50  --dbg_backtrace                         false
% 7.06/1.50  --dbg_dump_prop_clauses                 false
% 7.06/1.50  --dbg_dump_prop_clauses_file            -
% 7.06/1.50  --dbg_out_stat                          false
% 7.06/1.50  ------ Parsing...
% 7.06/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.06/1.50  
% 7.06/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.06/1.50  
% 7.06/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.06/1.50  
% 7.06/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.06/1.50  ------ Proving...
% 7.06/1.50  ------ Problem Properties 
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  clauses                                 34
% 7.06/1.50  conjectures                             13
% 7.06/1.50  EPR                                     12
% 7.06/1.50  Horn                                    24
% 7.06/1.50  unary                                   14
% 7.06/1.50  binary                                  8
% 7.06/1.50  lits                                    134
% 7.06/1.50  lits eq                                 16
% 7.06/1.50  fd_pure                                 0
% 7.06/1.50  fd_pseudo                               0
% 7.06/1.50  fd_cond                                 0
% 7.06/1.50  fd_pseudo_cond                          1
% 7.06/1.50  AC symbols                              0
% 7.06/1.50  
% 7.06/1.50  ------ Schedule dynamic 5 is on 
% 7.06/1.50  
% 7.06/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  ------ 
% 7.06/1.50  Current options:
% 7.06/1.50  ------ 
% 7.06/1.50  
% 7.06/1.50  ------ Input Options
% 7.06/1.50  
% 7.06/1.50  --out_options                           all
% 7.06/1.50  --tptp_safe_out                         true
% 7.06/1.50  --problem_path                          ""
% 7.06/1.50  --include_path                          ""
% 7.06/1.50  --clausifier                            res/vclausify_rel
% 7.06/1.50  --clausifier_options                    --mode clausify
% 7.06/1.50  --stdin                                 false
% 7.06/1.50  --stats_out                             all
% 7.06/1.50  
% 7.06/1.50  ------ General Options
% 7.06/1.50  
% 7.06/1.50  --fof                                   false
% 7.06/1.50  --time_out_real                         305.
% 7.06/1.50  --time_out_virtual                      -1.
% 7.06/1.50  --symbol_type_check                     false
% 7.06/1.50  --clausify_out                          false
% 7.06/1.50  --sig_cnt_out                           false
% 7.06/1.50  --trig_cnt_out                          false
% 7.06/1.50  --trig_cnt_out_tolerance                1.
% 7.06/1.50  --trig_cnt_out_sk_spl                   false
% 7.06/1.50  --abstr_cl_out                          false
% 7.06/1.50  
% 7.06/1.50  ------ Global Options
% 7.06/1.50  
% 7.06/1.50  --schedule                              default
% 7.06/1.50  --add_important_lit                     false
% 7.06/1.50  --prop_solver_per_cl                    1000
% 7.06/1.50  --min_unsat_core                        false
% 7.06/1.50  --soft_assumptions                      false
% 7.06/1.50  --soft_lemma_size                       3
% 7.06/1.50  --prop_impl_unit_size                   0
% 7.06/1.50  --prop_impl_unit                        []
% 7.06/1.50  --share_sel_clauses                     true
% 7.06/1.50  --reset_solvers                         false
% 7.06/1.50  --bc_imp_inh                            [conj_cone]
% 7.06/1.50  --conj_cone_tolerance                   3.
% 7.06/1.50  --extra_neg_conj                        none
% 7.06/1.50  --large_theory_mode                     true
% 7.06/1.50  --prolific_symb_bound                   200
% 7.06/1.50  --lt_threshold                          2000
% 7.06/1.50  --clause_weak_htbl                      true
% 7.06/1.50  --gc_record_bc_elim                     false
% 7.06/1.50  
% 7.06/1.50  ------ Preprocessing Options
% 7.06/1.50  
% 7.06/1.50  --preprocessing_flag                    true
% 7.06/1.50  --time_out_prep_mult                    0.1
% 7.06/1.50  --splitting_mode                        input
% 7.06/1.50  --splitting_grd                         true
% 7.06/1.50  --splitting_cvd                         false
% 7.06/1.50  --splitting_cvd_svl                     false
% 7.06/1.50  --splitting_nvd                         32
% 7.06/1.50  --sub_typing                            true
% 7.06/1.50  --prep_gs_sim                           true
% 7.06/1.50  --prep_unflatten                        true
% 7.06/1.50  --prep_res_sim                          true
% 7.06/1.50  --prep_upred                            true
% 7.06/1.50  --prep_sem_filter                       exhaustive
% 7.06/1.50  --prep_sem_filter_out                   false
% 7.06/1.50  --pred_elim                             true
% 7.06/1.50  --res_sim_input                         true
% 7.06/1.50  --eq_ax_congr_red                       true
% 7.06/1.50  --pure_diseq_elim                       true
% 7.06/1.50  --brand_transform                       false
% 7.06/1.50  --non_eq_to_eq                          false
% 7.06/1.50  --prep_def_merge                        true
% 7.06/1.50  --prep_def_merge_prop_impl              false
% 7.06/1.50  --prep_def_merge_mbd                    true
% 7.06/1.50  --prep_def_merge_tr_red                 false
% 7.06/1.50  --prep_def_merge_tr_cl                  false
% 7.06/1.50  --smt_preprocessing                     true
% 7.06/1.50  --smt_ac_axioms                         fast
% 7.06/1.50  --preprocessed_out                      false
% 7.06/1.50  --preprocessed_stats                    false
% 7.06/1.50  
% 7.06/1.50  ------ Abstraction refinement Options
% 7.06/1.50  
% 7.06/1.50  --abstr_ref                             []
% 7.06/1.50  --abstr_ref_prep                        false
% 7.06/1.50  --abstr_ref_until_sat                   false
% 7.06/1.50  --abstr_ref_sig_restrict                funpre
% 7.06/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.50  --abstr_ref_under                       []
% 7.06/1.50  
% 7.06/1.50  ------ SAT Options
% 7.06/1.50  
% 7.06/1.50  --sat_mode                              false
% 7.06/1.50  --sat_fm_restart_options                ""
% 7.06/1.50  --sat_gr_def                            false
% 7.06/1.50  --sat_epr_types                         true
% 7.06/1.50  --sat_non_cyclic_types                  false
% 7.06/1.50  --sat_finite_models                     false
% 7.06/1.50  --sat_fm_lemmas                         false
% 7.06/1.50  --sat_fm_prep                           false
% 7.06/1.50  --sat_fm_uc_incr                        true
% 7.06/1.50  --sat_out_model                         small
% 7.06/1.50  --sat_out_clauses                       false
% 7.06/1.50  
% 7.06/1.50  ------ QBF Options
% 7.06/1.50  
% 7.06/1.50  --qbf_mode                              false
% 7.06/1.50  --qbf_elim_univ                         false
% 7.06/1.50  --qbf_dom_inst                          none
% 7.06/1.50  --qbf_dom_pre_inst                      false
% 7.06/1.50  --qbf_sk_in                             false
% 7.06/1.50  --qbf_pred_elim                         true
% 7.06/1.50  --qbf_split                             512
% 7.06/1.50  
% 7.06/1.50  ------ BMC1 Options
% 7.06/1.50  
% 7.06/1.50  --bmc1_incremental                      false
% 7.06/1.50  --bmc1_axioms                           reachable_all
% 7.06/1.50  --bmc1_min_bound                        0
% 7.06/1.50  --bmc1_max_bound                        -1
% 7.06/1.50  --bmc1_max_bound_default                -1
% 7.06/1.50  --bmc1_symbol_reachability              true
% 7.06/1.50  --bmc1_property_lemmas                  false
% 7.06/1.50  --bmc1_k_induction                      false
% 7.06/1.50  --bmc1_non_equiv_states                 false
% 7.06/1.50  --bmc1_deadlock                         false
% 7.06/1.50  --bmc1_ucm                              false
% 7.06/1.50  --bmc1_add_unsat_core                   none
% 7.06/1.50  --bmc1_unsat_core_children              false
% 7.06/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.50  --bmc1_out_stat                         full
% 7.06/1.50  --bmc1_ground_init                      false
% 7.06/1.50  --bmc1_pre_inst_next_state              false
% 7.06/1.50  --bmc1_pre_inst_state                   false
% 7.06/1.50  --bmc1_pre_inst_reach_state             false
% 7.06/1.50  --bmc1_out_unsat_core                   false
% 7.06/1.50  --bmc1_aig_witness_out                  false
% 7.06/1.50  --bmc1_verbose                          false
% 7.06/1.50  --bmc1_dump_clauses_tptp                false
% 7.06/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.50  --bmc1_dump_file                        -
% 7.06/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.50  --bmc1_ucm_extend_mode                  1
% 7.06/1.50  --bmc1_ucm_init_mode                    2
% 7.06/1.50  --bmc1_ucm_cone_mode                    none
% 7.06/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.50  --bmc1_ucm_relax_model                  4
% 7.06/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.50  --bmc1_ucm_layered_model                none
% 7.06/1.50  --bmc1_ucm_max_lemma_size               10
% 7.06/1.50  
% 7.06/1.50  ------ AIG Options
% 7.06/1.50  
% 7.06/1.50  --aig_mode                              false
% 7.06/1.50  
% 7.06/1.50  ------ Instantiation Options
% 7.06/1.50  
% 7.06/1.50  --instantiation_flag                    true
% 7.06/1.50  --inst_sos_flag                         false
% 7.06/1.50  --inst_sos_phase                        true
% 7.06/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.50  --inst_lit_sel_side                     none
% 7.06/1.50  --inst_solver_per_active                1400
% 7.06/1.50  --inst_solver_calls_frac                1.
% 7.06/1.50  --inst_passive_queue_type               priority_queues
% 7.06/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.50  --inst_passive_queues_freq              [25;2]
% 7.06/1.50  --inst_dismatching                      true
% 7.06/1.50  --inst_eager_unprocessed_to_passive     true
% 7.06/1.50  --inst_prop_sim_given                   true
% 7.06/1.50  --inst_prop_sim_new                     false
% 7.06/1.50  --inst_subs_new                         false
% 7.06/1.50  --inst_eq_res_simp                      false
% 7.06/1.50  --inst_subs_given                       false
% 7.06/1.50  --inst_orphan_elimination               true
% 7.06/1.50  --inst_learning_loop_flag               true
% 7.06/1.50  --inst_learning_start                   3000
% 7.06/1.50  --inst_learning_factor                  2
% 7.06/1.50  --inst_start_prop_sim_after_learn       3
% 7.06/1.50  --inst_sel_renew                        solver
% 7.06/1.50  --inst_lit_activity_flag                true
% 7.06/1.50  --inst_restr_to_given                   false
% 7.06/1.50  --inst_activity_threshold               500
% 7.06/1.50  --inst_out_proof                        true
% 7.06/1.50  
% 7.06/1.50  ------ Resolution Options
% 7.06/1.50  
% 7.06/1.50  --resolution_flag                       false
% 7.06/1.50  --res_lit_sel                           adaptive
% 7.06/1.50  --res_lit_sel_side                      none
% 7.06/1.50  --res_ordering                          kbo
% 7.06/1.50  --res_to_prop_solver                    active
% 7.06/1.50  --res_prop_simpl_new                    false
% 7.06/1.50  --res_prop_simpl_given                  true
% 7.06/1.50  --res_passive_queue_type                priority_queues
% 7.06/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.50  --res_passive_queues_freq               [15;5]
% 7.06/1.50  --res_forward_subs                      full
% 7.06/1.50  --res_backward_subs                     full
% 7.06/1.50  --res_forward_subs_resolution           true
% 7.06/1.50  --res_backward_subs_resolution          true
% 7.06/1.50  --res_orphan_elimination                true
% 7.06/1.50  --res_time_limit                        2.
% 7.06/1.50  --res_out_proof                         true
% 7.06/1.50  
% 7.06/1.50  ------ Superposition Options
% 7.06/1.50  
% 7.06/1.50  --superposition_flag                    true
% 7.06/1.50  --sup_passive_queue_type                priority_queues
% 7.06/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.50  --demod_completeness_check              fast
% 7.06/1.50  --demod_use_ground                      true
% 7.06/1.50  --sup_to_prop_solver                    passive
% 7.06/1.50  --sup_prop_simpl_new                    true
% 7.06/1.50  --sup_prop_simpl_given                  true
% 7.06/1.50  --sup_fun_splitting                     false
% 7.06/1.50  --sup_smt_interval                      50000
% 7.06/1.50  
% 7.06/1.50  ------ Superposition Simplification Setup
% 7.06/1.50  
% 7.06/1.50  --sup_indices_passive                   []
% 7.06/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.50  --sup_full_bw                           [BwDemod]
% 7.06/1.50  --sup_immed_triv                        [TrivRules]
% 7.06/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.50  --sup_immed_bw_main                     []
% 7.06/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.50  
% 7.06/1.50  ------ Combination Options
% 7.06/1.50  
% 7.06/1.50  --comb_res_mult                         3
% 7.06/1.50  --comb_sup_mult                         2
% 7.06/1.50  --comb_inst_mult                        10
% 7.06/1.50  
% 7.06/1.50  ------ Debug Options
% 7.06/1.50  
% 7.06/1.50  --dbg_backtrace                         false
% 7.06/1.50  --dbg_dump_prop_clauses                 false
% 7.06/1.50  --dbg_dump_prop_clauses_file            -
% 7.06/1.50  --dbg_out_stat                          false
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  ------ Proving...
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  % SZS status Theorem for theBenchmark.p
% 7.06/1.50  
% 7.06/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.06/1.50  
% 7.06/1.50  fof(f16,conjecture,(
% 7.06/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.06/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f17,negated_conjecture,(
% 7.06/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.06/1.50    inference(negated_conjecture,[],[f16])).
% 7.06/1.50  
% 7.06/1.50  fof(f37,plain,(
% 7.06/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.06/1.50    inference(ennf_transformation,[],[f17])).
% 7.06/1.50  
% 7.06/1.50  fof(f38,plain,(
% 7.06/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.06/1.50    inference(flattening,[],[f37])).
% 7.06/1.50  
% 7.06/1.50  fof(f56,plain,(
% 7.06/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 7.06/1.51    introduced(choice_axiom,[])).
% 7.06/1.51  
% 7.06/1.51  fof(f55,plain,(
% 7.06/1.51    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 7.06/1.51    introduced(choice_axiom,[])).
% 7.06/1.51  
% 7.06/1.51  fof(f54,plain,(
% 7.06/1.51    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 7.06/1.51    introduced(choice_axiom,[])).
% 7.06/1.51  
% 7.06/1.51  fof(f53,plain,(
% 7.06/1.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.06/1.51    introduced(choice_axiom,[])).
% 7.06/1.51  
% 7.06/1.51  fof(f52,plain,(
% 7.06/1.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 7.06/1.51    introduced(choice_axiom,[])).
% 7.06/1.51  
% 7.06/1.51  fof(f51,plain,(
% 7.06/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 7.06/1.51    introduced(choice_axiom,[])).
% 7.06/1.51  
% 7.06/1.51  fof(f57,plain,(
% 7.06/1.51    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.06/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f38,f56,f55,f54,f53,f52,f51])).
% 7.06/1.51  
% 7.06/1.51  fof(f90,plain,(
% 7.06/1.51    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f5,axiom,(
% 7.06/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f21,plain,(
% 7.06/1.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.06/1.51    inference(ennf_transformation,[],[f5])).
% 7.06/1.51  
% 7.06/1.51  fof(f66,plain,(
% 7.06/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.06/1.51    inference(cnf_transformation,[],[f21])).
% 7.06/1.51  
% 7.06/1.51  fof(f6,axiom,(
% 7.06/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f67,plain,(
% 7.06/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.06/1.51    inference(cnf_transformation,[],[f6])).
% 7.06/1.51  
% 7.06/1.51  fof(f101,plain,(
% 7.06/1.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.06/1.51    inference(definition_unfolding,[],[f66,f67])).
% 7.06/1.51  
% 7.06/1.51  fof(f94,plain,(
% 7.06/1.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f13,axiom,(
% 7.06/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f31,plain,(
% 7.06/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.06/1.51    inference(ennf_transformation,[],[f13])).
% 7.06/1.51  
% 7.06/1.51  fof(f32,plain,(
% 7.06/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.06/1.51    inference(flattening,[],[f31])).
% 7.06/1.51  
% 7.06/1.51  fof(f78,plain,(
% 7.06/1.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f32])).
% 7.06/1.51  
% 7.06/1.51  fof(f92,plain,(
% 7.06/1.51    v1_funct_1(sK6)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f97,plain,(
% 7.06/1.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f95,plain,(
% 7.06/1.51    v1_funct_1(sK7)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f14,axiom,(
% 7.06/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f33,plain,(
% 7.06/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.06/1.51    inference(ennf_transformation,[],[f14])).
% 7.06/1.51  
% 7.06/1.51  fof(f34,plain,(
% 7.06/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.06/1.51    inference(flattening,[],[f33])).
% 7.06/1.51  
% 7.06/1.51  fof(f49,plain,(
% 7.06/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.06/1.51    inference(nnf_transformation,[],[f34])).
% 7.06/1.51  
% 7.06/1.51  fof(f50,plain,(
% 7.06/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.06/1.51    inference(flattening,[],[f49])).
% 7.06/1.51  
% 7.06/1.51  fof(f80,plain,(
% 7.06/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f50])).
% 7.06/1.51  
% 7.06/1.51  fof(f105,plain,(
% 7.06/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.06/1.51    inference(equality_resolution,[],[f80])).
% 7.06/1.51  
% 7.06/1.51  fof(f15,axiom,(
% 7.06/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f35,plain,(
% 7.06/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.06/1.51    inference(ennf_transformation,[],[f15])).
% 7.06/1.51  
% 7.06/1.51  fof(f36,plain,(
% 7.06/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.06/1.51    inference(flattening,[],[f35])).
% 7.06/1.51  
% 7.06/1.51  fof(f82,plain,(
% 7.06/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f36])).
% 7.06/1.51  
% 7.06/1.51  fof(f83,plain,(
% 7.06/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f36])).
% 7.06/1.51  
% 7.06/1.51  fof(f84,plain,(
% 7.06/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f36])).
% 7.06/1.51  
% 7.06/1.51  fof(f86,plain,(
% 7.06/1.51    ~v1_xboole_0(sK3)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f89,plain,(
% 7.06/1.51    ~v1_xboole_0(sK5)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f96,plain,(
% 7.06/1.51    v1_funct_2(sK7,sK5,sK3)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f87,plain,(
% 7.06/1.51    ~v1_xboole_0(sK4)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f93,plain,(
% 7.06/1.51    v1_funct_2(sK6,sK4,sK3)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f8,axiom,(
% 7.06/1.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f23,plain,(
% 7.06/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.06/1.51    inference(ennf_transformation,[],[f8])).
% 7.06/1.51  
% 7.06/1.51  fof(f24,plain,(
% 7.06/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.06/1.51    inference(flattening,[],[f23])).
% 7.06/1.51  
% 7.06/1.51  fof(f47,plain,(
% 7.06/1.51    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.06/1.51    inference(nnf_transformation,[],[f24])).
% 7.06/1.51  
% 7.06/1.51  fof(f70,plain,(
% 7.06/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f47])).
% 7.06/1.51  
% 7.06/1.51  fof(f91,plain,(
% 7.06/1.51    r1_subset_1(sK4,sK5)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f2,axiom,(
% 7.06/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f43,plain,(
% 7.06/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.06/1.51    inference(nnf_transformation,[],[f2])).
% 7.06/1.51  
% 7.06/1.51  fof(f60,plain,(
% 7.06/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f43])).
% 7.06/1.51  
% 7.06/1.51  fof(f100,plain,(
% 7.06/1.51    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.06/1.51    inference(definition_unfolding,[],[f60,f67])).
% 7.06/1.51  
% 7.06/1.51  fof(f9,axiom,(
% 7.06/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f25,plain,(
% 7.06/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.06/1.51    inference(ennf_transformation,[],[f9])).
% 7.06/1.51  
% 7.06/1.51  fof(f72,plain,(
% 7.06/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.06/1.51    inference(cnf_transformation,[],[f25])).
% 7.06/1.51  
% 7.06/1.51  fof(f4,axiom,(
% 7.06/1.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f65,plain,(
% 7.06/1.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f4])).
% 7.06/1.51  
% 7.06/1.51  fof(f7,axiom,(
% 7.06/1.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.06/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.51  
% 7.06/1.51  fof(f22,plain,(
% 7.06/1.51    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.06/1.51    inference(ennf_transformation,[],[f7])).
% 7.06/1.51  
% 7.06/1.51  fof(f46,plain,(
% 7.06/1.51    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.06/1.51    inference(nnf_transformation,[],[f22])).
% 7.06/1.51  
% 7.06/1.51  fof(f69,plain,(
% 7.06/1.51    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f46])).
% 7.06/1.51  
% 7.06/1.51  fof(f79,plain,(
% 7.06/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.06/1.51    inference(cnf_transformation,[],[f50])).
% 7.06/1.51  
% 7.06/1.51  fof(f106,plain,(
% 7.06/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.06/1.51    inference(equality_resolution,[],[f79])).
% 7.06/1.51  
% 7.06/1.51  fof(f98,plain,(
% 7.06/1.51    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f88,plain,(
% 7.06/1.51    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  fof(f85,plain,(
% 7.06/1.51    ~v1_xboole_0(sK2)),
% 7.06/1.51    inference(cnf_transformation,[],[f57])).
% 7.06/1.51  
% 7.06/1.51  cnf(c_34,negated_conjecture,
% 7.06/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.06/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1433,negated_conjecture,
% 7.06/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_34]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2313,plain,
% 7.06/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1433]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_8,plain,
% 7.06/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.06/1.51      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.06/1.51      inference(cnf_transformation,[],[f101]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1449,plain,
% 7.06/1.51      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.06/1.51      | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_8]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2298,plain,
% 7.06/1.51      ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
% 7.06/1.51      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3279,plain,
% 7.06/1.51      ( k9_subset_1(sK2,X0_57,sK5) = k1_setfam_1(k2_tarski(X0_57,sK5)) ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_2313,c_2298]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_30,negated_conjecture,
% 7.06/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.06/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1436,negated_conjecture,
% 7.06/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_30]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2310,plain,
% 7.06/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1436]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_19,plain,
% 7.06/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.06/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1445,plain,
% 7.06/1.51      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.06/1.51      | ~ v1_funct_1(X0_57)
% 7.06/1.51      | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_19]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2302,plain,
% 7.06/1.51      ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
% 7.06/1.51      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.06/1.51      | v1_funct_1(X2_57) != iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1445]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3665,plain,
% 7.06/1.51      ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57)
% 7.06/1.51      | v1_funct_1(sK6) != iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_2310,c_2302]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_32,negated_conjecture,
% 7.06/1.51      ( v1_funct_1(sK6) ),
% 7.06/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2764,plain,
% 7.06/1.51      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.06/1.51      | ~ v1_funct_1(sK6)
% 7.06/1.51      | k2_partfun1(X0_57,X1_57,sK6,X2_57) = k7_relat_1(sK6,X2_57) ),
% 7.06/1.51      inference(instantiation,[status(thm)],[c_1445]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2959,plain,
% 7.06/1.51      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.06/1.51      | ~ v1_funct_1(sK6)
% 7.06/1.51      | k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
% 7.06/1.51      inference(instantiation,[status(thm)],[c_2764]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3875,plain,
% 7.06/1.51      ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_3665,c_32,c_30,c_2959]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_27,negated_conjecture,
% 7.06/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.06/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1439,negated_conjecture,
% 7.06/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_27]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2307,plain,
% 7.06/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1439]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3664,plain,
% 7.06/1.51      ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57)
% 7.06/1.51      | v1_funct_1(sK7) != iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_2307,c_2302]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_29,negated_conjecture,
% 7.06/1.51      ( v1_funct_1(sK7) ),
% 7.06/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2759,plain,
% 7.06/1.51      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.06/1.51      | ~ v1_funct_1(sK7)
% 7.06/1.51      | k2_partfun1(X0_57,X1_57,sK7,X2_57) = k7_relat_1(sK7,X2_57) ),
% 7.06/1.51      inference(instantiation,[status(thm)],[c_1445]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2954,plain,
% 7.06/1.51      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.06/1.51      | ~ v1_funct_1(sK7)
% 7.06/1.51      | k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
% 7.06/1.51      inference(instantiation,[status(thm)],[c_2759]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3869,plain,
% 7.06/1.51      ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_3664,c_29,c_27,c_2954]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_21,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_1(X3)
% 7.06/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X1)
% 7.06/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.06/1.51      inference(cnf_transformation,[],[f105]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_25,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_1(X3)
% 7.06/1.51      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X1) ),
% 7.06/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_24,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_1(X3)
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X1) ),
% 7.06/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_23,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_1(X3)
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X1) ),
% 7.06/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_225,plain,
% 7.06/1.51      ( ~ v1_funct_1(X3)
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X1)
% 7.06/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_21,c_25,c_24,c_23]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_226,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_1(X3)
% 7.06/1.51      | v1_xboole_0(X1)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.06/1.51      inference(renaming,[status(thm)],[c_225]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1426,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.06/1.51      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.06/1.51      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.06/1.51      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.06/1.51      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.06/1.51      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.06/1.51      | ~ v1_funct_1(X0_57)
% 7.06/1.51      | ~ v1_funct_1(X3_57)
% 7.06/1.51      | v1_xboole_0(X2_57)
% 7.06/1.51      | v1_xboole_0(X1_57)
% 7.06/1.51      | v1_xboole_0(X4_57)
% 7.06/1.51      | v1_xboole_0(X5_57)
% 7.06/1.51      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_226]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2320,plain,
% 7.06/1.51      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
% 7.06/1.51      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.06/1.51      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.06/1.51      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.06/1.51      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.06/1.51      | v1_funct_1(X2_57) != iProver_top
% 7.06/1.51      | v1_funct_1(X5_57) != iProver_top
% 7.06/1.51      | v1_xboole_0(X3_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X4_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X1_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1426]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_7144,plain,
% 7.06/1.51      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.06/1.51      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.06/1.51      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.06/1.51      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.06/1.51      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | v1_funct_1(X1_57) != iProver_top
% 7.06/1.51      | v1_funct_1(sK7) != iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X2_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(sK3) = iProver_top
% 7.06/1.51      | v1_xboole_0(sK5) = iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_3869,c_2320]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_38,negated_conjecture,
% 7.06/1.51      ( ~ v1_xboole_0(sK3) ),
% 7.06/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_41,plain,
% 7.06/1.51      ( v1_xboole_0(sK3) != iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_35,negated_conjecture,
% 7.06/1.51      ( ~ v1_xboole_0(sK5) ),
% 7.06/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_44,plain,
% 7.06/1.51      ( v1_xboole_0(sK5) != iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_50,plain,
% 7.06/1.51      ( v1_funct_1(sK7) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_28,negated_conjecture,
% 7.06/1.51      ( v1_funct_2(sK7,sK5,sK3) ),
% 7.06/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_51,plain,
% 7.06/1.51      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_52,plain,
% 7.06/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9593,plain,
% 7.06/1.51      ( v1_funct_1(X1_57) != iProver_top
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.06/1.51      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.06/1.51      | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.06/1.51      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X2_57) = iProver_top ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_7144,c_41,c_44,c_50,c_51,c_52]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9594,plain,
% 7.06/1.51      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.06/1.51      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.06/1.51      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | v1_funct_1(X1_57) != iProver_top
% 7.06/1.51      | v1_xboole_0(X2_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top ),
% 7.06/1.51      inference(renaming,[status(thm)],[c_9593]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9609,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.06/1.51      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.06/1.51      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.06/1.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | v1_funct_1(sK6) != iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_3875,c_9594]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_37,negated_conjecture,
% 7.06/1.51      ( ~ v1_xboole_0(sK4) ),
% 7.06/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_42,plain,
% 7.06/1.51      ( v1_xboole_0(sK4) != iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_47,plain,
% 7.06/1.51      ( v1_funct_1(sK6) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_31,negated_conjecture,
% 7.06/1.51      ( v1_funct_2(sK6,sK4,sK3) ),
% 7.06/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_48,plain,
% 7.06/1.51      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_49,plain,
% 7.06/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9792,plain,
% 7.06/1.51      ( v1_xboole_0(X0_57) = iProver_top
% 7.06/1.51      | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.06/1.51      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_9609,c_42,c_47,c_48,c_49]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9793,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.06/1.51      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top ),
% 7.06/1.51      inference(renaming,[status(thm)],[c_9792]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9803,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.06/1.51      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_3279,c_9793]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_12,plain,
% 7.06/1.51      ( ~ r1_subset_1(X0,X1)
% 7.06/1.51      | r1_xboole_0(X0,X1)
% 7.06/1.51      | v1_xboole_0(X0)
% 7.06/1.51      | v1_xboole_0(X1) ),
% 7.06/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_33,negated_conjecture,
% 7.06/1.51      ( r1_subset_1(sK4,sK5) ),
% 7.06/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_592,plain,
% 7.06/1.51      ( r1_xboole_0(X0,X1)
% 7.06/1.51      | v1_xboole_0(X0)
% 7.06/1.51      | v1_xboole_0(X1)
% 7.06/1.51      | sK5 != X1
% 7.06/1.51      | sK4 != X0 ),
% 7.06/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_33]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_593,plain,
% 7.06/1.51      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 7.06/1.51      inference(unflattening,[status(thm)],[c_592]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_595,plain,
% 7.06/1.51      ( r1_xboole_0(sK4,sK5) ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_593,c_37,c_35]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1425,plain,
% 7.06/1.51      ( r1_xboole_0(sK4,sK5) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_595]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2321,plain,
% 7.06/1.51      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1425]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3,plain,
% 7.06/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.06/1.51      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.06/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1454,plain,
% 7.06/1.51      ( ~ r1_xboole_0(X0_57,X1_57)
% 7.06/1.51      | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2293,plain,
% 7.06/1.51      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
% 7.06/1.51      | r1_xboole_0(X0_57,X1_57) != iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1454]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3231,plain,
% 7.06/1.51      ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_2321,c_2293]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_13,plain,
% 7.06/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | v1_relat_1(X0) ),
% 7.06/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1446,plain,
% 7.06/1.51      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.06/1.51      | v1_relat_1(X0_57) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_13]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2301,plain,
% 7.06/1.51      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.06/1.51      | v1_relat_1(X0_57) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1446]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3346,plain,
% 7.06/1.51      ( v1_relat_1(sK7) = iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_2307,c_2301]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_7,plain,
% 7.06/1.51      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.06/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1450,plain,
% 7.06/1.51      ( r1_xboole_0(X0_57,k1_xboole_0) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_7]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2297,plain,
% 7.06/1.51      ( r1_xboole_0(X0_57,k1_xboole_0) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9,plain,
% 7.06/1.51      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.06/1.51      | ~ v1_relat_1(X0)
% 7.06/1.51      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.06/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1448,plain,
% 7.06/1.51      ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.06/1.51      | ~ v1_relat_1(X0_57)
% 7.06/1.51      | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_9]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2299,plain,
% 7.06/1.51      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.06/1.51      | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
% 7.06/1.51      | v1_relat_1(X0_57) != iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1448]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3408,plain,
% 7.06/1.51      ( k7_relat_1(X0_57,k1_xboole_0) = k1_xboole_0
% 7.06/1.51      | v1_relat_1(X0_57) != iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_2297,c_2299]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6324,plain,
% 7.06/1.51      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_3346,c_3408]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9804,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.06/1.51      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(light_normalisation,[status(thm)],[c_9803,c_3231,c_6324]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9805,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.06/1.51      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k1_xboole_0
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(demodulation,[status(thm)],[c_9804,c_3279]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3347,plain,
% 7.06/1.51      ( v1_relat_1(sK6) = iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_2310,c_2301]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6325,plain,
% 7.06/1.51      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_3347,c_3408]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9806,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.06/1.51      | k1_xboole_0 != k1_xboole_0
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(light_normalisation,[status(thm)],[c_9805,c_3231,c_6325]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_9807,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(equality_resolution_simp,[status(thm)],[c_9806]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_22,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_1(X3)
% 7.06/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X1)
% 7.06/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.06/1.51      inference(cnf_transformation,[],[f106]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_218,plain,
% 7.06/1.51      ( ~ v1_funct_1(X3)
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X1)
% 7.06/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_22,c_25,c_24,c_23]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_219,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.06/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.06/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.06/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.06/1.51      | ~ v1_funct_1(X0)
% 7.06/1.51      | ~ v1_funct_1(X3)
% 7.06/1.51      | v1_xboole_0(X1)
% 7.06/1.51      | v1_xboole_0(X2)
% 7.06/1.51      | v1_xboole_0(X4)
% 7.06/1.51      | v1_xboole_0(X5)
% 7.06/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.06/1.51      inference(renaming,[status(thm)],[c_218]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1427,plain,
% 7.06/1.51      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.06/1.51      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.06/1.51      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.06/1.51      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.06/1.51      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.06/1.51      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.06/1.51      | ~ v1_funct_1(X0_57)
% 7.06/1.51      | ~ v1_funct_1(X3_57)
% 7.06/1.51      | v1_xboole_0(X2_57)
% 7.06/1.51      | v1_xboole_0(X1_57)
% 7.06/1.51      | v1_xboole_0(X4_57)
% 7.06/1.51      | v1_xboole_0(X5_57)
% 7.06/1.51      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_219]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2319,plain,
% 7.06/1.51      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
% 7.06/1.51      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.06/1.51      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.06/1.51      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.06/1.51      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.06/1.51      | v1_funct_1(X2_57) != iProver_top
% 7.06/1.51      | v1_funct_1(X5_57) != iProver_top
% 7.06/1.51      | v1_xboole_0(X3_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X4_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X1_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_1427]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_5933,plain,
% 7.06/1.51      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.06/1.51      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.06/1.51      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.06/1.51      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.06/1.51      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | v1_funct_1(X1_57) != iProver_top
% 7.06/1.51      | v1_funct_1(sK7) != iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X2_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(sK3) = iProver_top
% 7.06/1.51      | v1_xboole_0(sK5) = iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_3869,c_2319]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6512,plain,
% 7.06/1.51      ( v1_funct_1(X1_57) != iProver_top
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.06/1.51      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.06/1.51      | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.06/1.51      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X2_57) = iProver_top ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_5933,c_41,c_44,c_50,c_51,c_52]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6513,plain,
% 7.06/1.51      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.06/1.51      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.06/1.51      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.06/1.51      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.06/1.51      | v1_funct_1(X1_57) != iProver_top
% 7.06/1.51      | v1_xboole_0(X2_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top ),
% 7.06/1.51      inference(renaming,[status(thm)],[c_6512]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6528,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.06/1.51      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.06/1.51      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.06/1.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | v1_funct_1(sK6) != iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top
% 7.06/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_3875,c_6513]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6739,plain,
% 7.06/1.51      ( v1_xboole_0(X0_57) = iProver_top
% 7.06/1.51      | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.06/1.51      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.06/1.51      inference(global_propositional_subsumption,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_6528,c_42,c_47,c_48,c_49]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6740,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.06/1.51      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.06/1.51      | v1_xboole_0(X0_57) = iProver_top ),
% 7.06/1.51      inference(renaming,[status(thm)],[c_6739]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6750,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.06/1.51      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(superposition,[status(thm)],[c_3279,c_6740]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6751,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.06/1.51      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(light_normalisation,[status(thm)],[c_6750,c_3231,c_6324]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6752,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.06/1.51      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k1_xboole_0
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(demodulation,[status(thm)],[c_6751,c_3279]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6753,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.06/1.51      | k1_xboole_0 != k1_xboole_0
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(light_normalisation,[status(thm)],[c_6752,c_3231,c_6325]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6754,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.06/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.06/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.06/1.51      inference(equality_resolution_simp,[status(thm)],[c_6753]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_26,negated_conjecture,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.06/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.06/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.06/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_1440,negated_conjecture,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.06/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.06/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.06/1.51      inference(subtyping,[status(esa)],[c_26]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3449,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.06/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.06/1.51      | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 7.06/1.51      inference(demodulation,[status(thm)],[c_3279,c_1440]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3450,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.06/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.06/1.51      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
% 7.06/1.51      inference(light_normalisation,[status(thm)],[c_3449,c_3231]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3873,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.06/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.06/1.51      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.06/1.51      inference(demodulation,[status(thm)],[c_3869,c_3450]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3976,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.06/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.06/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.06/1.51      inference(demodulation,[status(thm)],[c_3873,c_3875]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_6422,plain,
% 7.06/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.06/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.06/1.51      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 7.06/1.51      inference(demodulation,[status(thm)],[c_6324,c_3976]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3193,plain,
% 7.06/1.51      ( r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) ),
% 7.06/1.51      inference(instantiation,[status(thm)],[c_1450]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2886,plain,
% 7.06/1.51      ( ~ r1_xboole_0(k1_relat_1(sK6),X0_57)
% 7.06/1.51      | ~ v1_relat_1(sK6)
% 7.06/1.51      | k7_relat_1(sK6,X0_57) = k1_xboole_0 ),
% 7.06/1.51      inference(instantiation,[status(thm)],[c_1448]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_3192,plain,
% 7.06/1.51      ( ~ r1_xboole_0(k1_relat_1(sK6),k1_xboole_0)
% 7.06/1.51      | ~ v1_relat_1(sK6)
% 7.06/1.51      | k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.06/1.51      inference(instantiation,[status(thm)],[c_2886]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_2675,plain,
% 7.06/1.51      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.06/1.51      | v1_relat_1(sK6) ),
% 7.06/1.51      inference(instantiation,[status(thm)],[c_1446]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_45,plain,
% 7.06/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_36,negated_conjecture,
% 7.06/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 7.06/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_43,plain,
% 7.06/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_39,negated_conjecture,
% 7.06/1.51      ( ~ v1_xboole_0(sK2) ),
% 7.06/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(c_40,plain,
% 7.06/1.51      ( v1_xboole_0(sK2) != iProver_top ),
% 7.06/1.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.06/1.51  
% 7.06/1.51  cnf(contradiction,plain,
% 7.06/1.51      ( $false ),
% 7.06/1.51      inference(minisat,
% 7.06/1.51                [status(thm)],
% 7.06/1.51                [c_9807,c_6754,c_6422,c_3193,c_3192,c_2675,c_30,c_45,
% 7.06/1.51                 c_43,c_40]) ).
% 7.06/1.51  
% 7.06/1.51  
% 7.06/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.06/1.51  
% 7.06/1.51  ------                               Statistics
% 7.06/1.51  
% 7.06/1.51  ------ General
% 7.06/1.51  
% 7.06/1.51  abstr_ref_over_cycles:                  0
% 7.06/1.51  abstr_ref_under_cycles:                 0
% 7.06/1.51  gc_basic_clause_elim:                   0
% 7.06/1.51  forced_gc_time:                         0
% 7.06/1.51  parsing_time:                           0.014
% 7.06/1.51  unif_index_cands_time:                  0.
% 7.06/1.51  unif_index_add_time:                    0.
% 7.06/1.51  orderings_time:                         0.
% 7.06/1.51  out_proof_time:                         0.018
% 7.06/1.51  total_time:                             0.678
% 7.06/1.51  num_of_symbols:                         64
% 7.06/1.51  num_of_terms:                           20029
% 7.06/1.51  
% 7.06/1.51  ------ Preprocessing
% 7.06/1.51  
% 7.06/1.51  num_of_splits:                          0
% 7.06/1.51  num_of_split_atoms:                     0
% 7.06/1.51  num_of_reused_defs:                     0
% 7.06/1.51  num_eq_ax_congr_red:                    32
% 7.06/1.51  num_of_sem_filtered_clauses:            1
% 7.06/1.51  num_of_subtypes:                        4
% 7.06/1.51  monotx_restored_types:                  0
% 7.06/1.51  sat_num_of_epr_types:                   0
% 7.06/1.51  sat_num_of_non_cyclic_types:            0
% 7.06/1.51  sat_guarded_non_collapsed_types:        1
% 7.06/1.51  num_pure_diseq_elim:                    0
% 7.06/1.51  simp_replaced_by:                       0
% 7.06/1.51  res_preprocessed:                       178
% 7.06/1.51  prep_upred:                             0
% 7.06/1.51  prep_unflattend:                        48
% 7.06/1.51  smt_new_axioms:                         0
% 7.06/1.51  pred_elim_cands:                        7
% 7.06/1.51  pred_elim:                              3
% 7.06/1.51  pred_elim_cl:                           5
% 7.06/1.51  pred_elim_cycles:                       7
% 7.06/1.51  merged_defs:                            8
% 7.06/1.51  merged_defs_ncl:                        0
% 7.06/1.51  bin_hyper_res:                          8
% 7.06/1.51  prep_cycles:                            4
% 7.06/1.51  pred_elim_time:                         0.01
% 7.06/1.51  splitting_time:                         0.
% 7.06/1.51  sem_filter_time:                        0.
% 7.06/1.51  monotx_time:                            0.
% 7.06/1.51  subtype_inf_time:                       0.002
% 7.06/1.51  
% 7.06/1.51  ------ Problem properties
% 7.06/1.51  
% 7.06/1.51  clauses:                                34
% 7.06/1.51  conjectures:                            13
% 7.06/1.51  epr:                                    12
% 7.06/1.51  horn:                                   24
% 7.06/1.51  ground:                                 14
% 7.06/1.51  unary:                                  14
% 7.06/1.51  binary:                                 8
% 7.06/1.51  lits:                                   134
% 7.06/1.51  lits_eq:                                16
% 7.06/1.51  fd_pure:                                0
% 7.06/1.51  fd_pseudo:                              0
% 7.06/1.51  fd_cond:                                0
% 7.06/1.51  fd_pseudo_cond:                         1
% 7.06/1.51  ac_symbols:                             0
% 7.06/1.51  
% 7.06/1.51  ------ Propositional Solver
% 7.06/1.51  
% 7.06/1.51  prop_solver_calls:                      29
% 7.06/1.51  prop_fast_solver_calls:                 2210
% 7.06/1.51  smt_solver_calls:                       0
% 7.06/1.51  smt_fast_solver_calls:                  0
% 7.06/1.51  prop_num_of_clauses:                    3832
% 7.06/1.51  prop_preprocess_simplified:             9011
% 7.06/1.51  prop_fo_subsumed:                       97
% 7.06/1.51  prop_solver_time:                       0.
% 7.06/1.51  smt_solver_time:                        0.
% 7.06/1.51  smt_fast_solver_time:                   0.
% 7.06/1.51  prop_fast_solver_time:                  0.
% 7.06/1.51  prop_unsat_core_time:                   0.001
% 7.06/1.51  
% 7.06/1.51  ------ QBF
% 7.06/1.51  
% 7.06/1.51  qbf_q_res:                              0
% 7.06/1.51  qbf_num_tautologies:                    0
% 7.06/1.51  qbf_prep_cycles:                        0
% 7.06/1.51  
% 7.06/1.51  ------ BMC1
% 7.06/1.51  
% 7.06/1.51  bmc1_current_bound:                     -1
% 7.06/1.51  bmc1_last_solved_bound:                 -1
% 7.06/1.51  bmc1_unsat_core_size:                   -1
% 7.06/1.51  bmc1_unsat_core_parents_size:           -1
% 7.06/1.51  bmc1_merge_next_fun:                    0
% 7.06/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.06/1.51  
% 7.06/1.51  ------ Instantiation
% 7.06/1.51  
% 7.06/1.51  inst_num_of_clauses:                    982
% 7.06/1.51  inst_num_in_passive:                    430
% 7.06/1.51  inst_num_in_active:                     476
% 7.06/1.51  inst_num_in_unprocessed:                76
% 7.06/1.51  inst_num_of_loops:                      490
% 7.06/1.51  inst_num_of_learning_restarts:          0
% 7.06/1.51  inst_num_moves_active_passive:          10
% 7.06/1.51  inst_lit_activity:                      0
% 7.06/1.51  inst_lit_activity_moves:                0
% 7.06/1.51  inst_num_tautologies:                   0
% 7.06/1.51  inst_num_prop_implied:                  0
% 7.06/1.51  inst_num_existing_simplified:           0
% 7.06/1.51  inst_num_eq_res_simplified:             0
% 7.06/1.51  inst_num_child_elim:                    0
% 7.06/1.51  inst_num_of_dismatching_blockings:      88
% 7.06/1.51  inst_num_of_non_proper_insts:           700
% 7.06/1.51  inst_num_of_duplicates:                 0
% 7.06/1.51  inst_inst_num_from_inst_to_res:         0
% 7.06/1.51  inst_dismatching_checking_time:         0.
% 7.06/1.51  
% 7.06/1.51  ------ Resolution
% 7.06/1.51  
% 7.06/1.51  res_num_of_clauses:                     0
% 7.06/1.51  res_num_in_passive:                     0
% 7.06/1.51  res_num_in_active:                      0
% 7.06/1.51  res_num_of_loops:                       182
% 7.06/1.51  res_forward_subset_subsumed:            39
% 7.06/1.51  res_backward_subset_subsumed:           2
% 7.06/1.51  res_forward_subsumed:                   0
% 7.06/1.51  res_backward_subsumed:                  0
% 7.06/1.51  res_forward_subsumption_resolution:     1
% 7.06/1.51  res_backward_subsumption_resolution:    0
% 7.06/1.51  res_clause_to_clause_subsumption:       592
% 7.06/1.51  res_orphan_elimination:                 0
% 7.06/1.51  res_tautology_del:                      55
% 7.06/1.51  res_num_eq_res_simplified:              0
% 7.06/1.51  res_num_sel_changes:                    0
% 7.06/1.51  res_moves_from_active_to_pass:          0
% 7.06/1.51  
% 7.06/1.51  ------ Superposition
% 7.06/1.51  
% 7.06/1.51  sup_time_total:                         0.
% 7.06/1.51  sup_time_generating:                    0.
% 7.06/1.51  sup_time_sim_full:                      0.
% 7.06/1.51  sup_time_sim_immed:                     0.
% 7.06/1.51  
% 7.06/1.51  sup_num_of_clauses:                     129
% 7.06/1.51  sup_num_in_active:                      94
% 7.06/1.51  sup_num_in_passive:                     35
% 7.06/1.51  sup_num_of_loops:                       96
% 7.06/1.51  sup_fw_superposition:                   104
% 7.06/1.51  sup_bw_superposition:                   29
% 7.06/1.51  sup_immediate_simplified:               61
% 7.06/1.51  sup_given_eliminated:                   0
% 7.06/1.51  comparisons_done:                       0
% 7.06/1.51  comparisons_avoided:                    0
% 7.06/1.51  
% 7.06/1.51  ------ Simplifications
% 7.06/1.51  
% 7.06/1.51  
% 7.06/1.51  sim_fw_subset_subsumed:                 8
% 7.06/1.51  sim_bw_subset_subsumed:                 0
% 7.06/1.51  sim_fw_subsumed:                        6
% 7.06/1.51  sim_bw_subsumed:                        0
% 7.06/1.51  sim_fw_subsumption_res:                 0
% 7.06/1.51  sim_bw_subsumption_res:                 0
% 7.06/1.51  sim_tautology_del:                      1
% 7.06/1.51  sim_eq_tautology_del:                   2
% 7.06/1.51  sim_eq_res_simp:                        5
% 7.06/1.51  sim_fw_demodulated:                     20
% 7.06/1.51  sim_bw_demodulated:                     3
% 7.06/1.51  sim_light_normalised:                   39
% 7.06/1.51  sim_joinable_taut:                      0
% 7.06/1.51  sim_joinable_simp:                      0
% 7.06/1.51  sim_ac_normalised:                      0
% 7.06/1.51  sim_smt_subsumption:                    0
% 7.06/1.51  
%------------------------------------------------------------------------------
