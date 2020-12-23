%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:24 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  322 (6547 expanded)
%              Number of clauses        :  211 (1507 expanded)
%              Number of leaves         :   31 (2616 expanded)
%              Depth                    :   26
%              Number of atoms          : 1593 (84088 expanded)
%              Number of equality atoms :  680 (19529 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f66,plain,(
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

fof(f65,plain,(
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

fof(f64,plain,(
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

fof(f63,plain,(
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

fof(f62,plain,(
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

fof(f61,plain,
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

fof(f67,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f53,f66,f65,f64,f63,f62,f61])).

fof(f105,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f112,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f109,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f67])).

fof(f107,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f121,plain,(
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
    inference(equality_resolution,[],[f94])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f102,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f108,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f104,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f111,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f106,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f42])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f103,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f120,plain,(
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
    inference(equality_resolution,[],[f95])).

fof(f113,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f67])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r1_xboole_0(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
     => r1_xboole_0(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f56])).

fof(f88,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1745,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1775,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3679,plain,
    ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_1745,c_1775])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1752,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1757,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5527,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_1757])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2400,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2842,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_2400])).

cnf(c_5783,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5527,c_34,c_32,c_2842])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1749,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5528,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1757])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2405,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2847,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2405])).

cnf(c_5789,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5528,c_37,c_35,c_2847])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f97])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f98])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f99])).

cnf(c_442,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_30,c_29,c_28])).

cnf(c_443,plain,
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
    inference(renaming,[status(thm)],[c_442])).

cnf(c_1739,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1774,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2053,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
    | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
    | v1_funct_2(X5,X4,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1739,c_1774])).

cnf(c_12072,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5789,c_2053])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_46,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_47,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_52,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_53,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_30541,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12072,c_46,c_47,c_52,c_53,c_54])).

cnf(c_30542,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_30541])).

cnf(c_30553,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5783,c_30542])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_49,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_55,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_56,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_57,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30976,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30553,c_49,c_55,c_56,c_57])).

cnf(c_30986,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3679,c_30976])).

cnf(c_38,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1746,plain,
    ( r1_subset_1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_16,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1764,plain,
    ( r1_subset_1(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4317,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_1764])).

cnf(c_51,plain,
    ( r1_subset_1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2316,plain,
    ( ~ r1_subset_1(sK3,sK4)
    | r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2317,plain,
    ( r1_subset_1(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2316])).

cnf(c_4693,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4317,c_47,c_49,c_51,c_2317])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1777,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4698,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4693,c_1777])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1763,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3004,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_1763])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1760,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2955,plain,
    ( v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_partfun1(sK6,sK4) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_1760])).

cnf(c_2394,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2836,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | v1_partfun1(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2394])).

cnf(c_2837,plain,
    ( v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_partfun1(sK6,sK4) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2836])).

cnf(c_3231,plain,
    ( v1_partfun1(sK6,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2955,c_46,c_55,c_56,c_57,c_2837])).

cnf(c_23,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1758,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5507,plain,
    ( k1_relat_1(sK6) = sK4
    | v4_relat_1(sK6,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3231,c_1758])).

cnf(c_2258,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2310,plain,
    ( v4_relat_1(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2757,plain,
    ( ~ v1_partfun1(X0,sK4)
    | ~ v4_relat_1(X0,sK4)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4405,plain,
    ( ~ v1_partfun1(sK6,sK4)
    | ~ v4_relat_1(sK6,sK4)
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_2757])).

cnf(c_5974,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5507,c_43,c_34,c_33,c_32,c_2258,c_2310,c_2836,c_4405])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1769,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5986,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5974,c_1769])).

cnf(c_2259,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2258])).

cnf(c_7164,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5986,c_57,c_2259])).

cnf(c_7165,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7164])).

cnf(c_7173,plain,
    ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4693,c_7165])).

cnf(c_14,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1766,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7181,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7173,c_1766])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7197,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7181,c_11])).

cnf(c_7807,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7197,c_57,c_2259])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1770,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7812,plain,
    ( k9_relat_1(k7_relat_1(X0,sK3),k1_xboole_0) = k9_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7807,c_1770])).

cnf(c_9032,plain,
    ( k9_relat_1(k7_relat_1(sK6,sK3),k1_xboole_0) = k9_relat_1(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3004,c_7812])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1773,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7182,plain,
    ( v1_relat_1(sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7173,c_1773])).

cnf(c_7408,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7182,c_57,c_2259])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1772,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7415,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7408,c_1772])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7417,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7415,c_10,c_11])).

cnf(c_9037,plain,
    ( k9_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9032,c_7173,c_7417])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1771,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3150,plain,
    ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_3004,c_1771])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1768,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3654,plain,
    ( k9_relat_1(sK6,X0) != k1_xboole_0
    | k7_relat_1(sK6,X0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3150,c_1768])).

cnf(c_2474,plain,
    ( v1_relat_1(k7_relat_1(sK6,X0))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3668,plain,
    ( ~ v1_relat_1(k7_relat_1(sK6,X0))
    | k9_relat_1(sK6,X0) != k1_xboole_0
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3654])).

cnf(c_4199,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | k9_relat_1(sK6,X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3654,c_32,c_2258,c_2474,c_3668])).

cnf(c_4200,plain,
    ( k9_relat_1(sK6,X0) != k1_xboole_0
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4199])).

cnf(c_9083,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9037,c_4200])).

cnf(c_30987,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30986,c_4698,c_9083])).

cnf(c_1755,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1998,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1755,c_1774])).

cnf(c_8540,plain,
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
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1998,c_1757])).

cnf(c_1753,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1946,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1753,c_1774])).

cnf(c_19033,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
    | v1_funct_2(X5,X2,X3) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8540,c_1946])).

cnf(c_19036,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_19033])).

cnf(c_19321,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19036,c_46,c_49,c_55,c_56])).

cnf(c_19322,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_19321])).

cnf(c_19334,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_19322])).

cnf(c_19714,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19334,c_47,c_52,c_53])).

cnf(c_19723,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_19714])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2450,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK5,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_tmap_1(X4,X2,X3,X1,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X3,X1),X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2916,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | m1_subset_1(k1_tmap_1(X2,sK2,sK3,X1,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,sK3,X1),sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_3289,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
    | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X1,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X1),sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2916])).

cnf(c_3895,plain,
    ( ~ v1_funct_2(X0,sK4,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3289])).

cnf(c_5472,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3895])).

cnf(c_6865,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
    | ~ v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2444,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK5,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k1_tmap_1(X4,X2,X3,X1,sK5,X0))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2873,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k1_tmap_1(X2,sK2,sK3,X1,sK5,X0))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2444])).

cnf(c_5884,plain,
    ( ~ v1_funct_2(sK6,X0,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
    | v1_funct_1(k1_tmap_1(X1,sK2,sK3,X0,sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_7388,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | v1_funct_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5884])).

cnf(c_11660,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7388])).

cnf(c_19728,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19723,c_44,c_43,c_42,c_41,c_40,c_39,c_37,c_36,c_35,c_34,c_33,c_32,c_5472,c_6865,c_11660])).

cnf(c_30988,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30987,c_3679,c_19728])).

cnf(c_30989,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30988,c_4698])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_449,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_30,c_29,c_28])).

cnf(c_450,plain,
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
    inference(renaming,[status(thm)],[c_449])).

cnf(c_1738,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_2025,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
    | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
    | v1_funct_2(X5,X4,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1738,c_1774])).

cnf(c_9847,plain,
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
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5783,c_2025])).

cnf(c_27897,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9847,c_46,c_49,c_55,c_56,c_57])).

cnf(c_27898,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_27897])).

cnf(c_27915,plain,
    ( k2_partfun1(X0,sK2,X1,k1_setfam_1(k2_tarski(X0,sK4))) != k7_relat_1(sK6,k9_subset_1(sK1,X0,sK4))
    | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3679,c_27898])).

cnf(c_27924,plain,
    ( k2_partfun1(X0,sK2,X1,k1_setfam_1(k2_tarski(X0,sK4))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(X0,sK4)))
    | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27915,c_3679])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_28512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | k2_partfun1(X0,sK2,X1,k1_setfam_1(k2_tarski(X0,sK4))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(X0,sK4)))
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27924,c_50])).

cnf(c_28513,plain,
    ( k2_partfun1(X0,sK2,X1,k1_setfam_1(k2_tarski(X0,sK4))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(X0,sK4)))
    | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_28512])).

cnf(c_28524,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4)))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5789,c_28513])).

cnf(c_28625,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28524,c_4698,c_9083])).

cnf(c_28626,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28625,c_19728])).

cnf(c_31,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3973,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK4,sK2,sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k2_partfun1(sK3,sK2,sK5,k1_setfam_1(k2_tarski(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_3679,c_31])).

cnf(c_4778,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4698,c_3973])).

cnf(c_5787,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5783,c_4778])).

cnf(c_6116,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5787,c_5789])).

cnf(c_9205,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9083,c_6116])).

cnf(c_19732,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19728,c_9205])).

cnf(c_19733,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19732,c_19728])).

cnf(c_3005,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1763])).

cnf(c_19,plain,
    ( r1_xboole_0(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1761,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2956,plain,
    ( v1_funct_2(sK5,sK3,sK2) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1760])).

cnf(c_2397,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | v1_partfun1(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2839,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | v1_partfun1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_2840,plain,
    ( v1_funct_2(sK5,sK3,sK2) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2839])).

cnf(c_3237,plain,
    ( v1_partfun1(sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2956,c_46,c_52,c_53,c_54,c_2840])).

cnf(c_5508,plain,
    ( k1_relat_1(sK5) = sK3
    | v4_relat_1(sK5,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3237,c_1758])).

cnf(c_2261,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2313,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2810,plain,
    ( ~ v1_partfun1(X0,sK3)
    | ~ v4_relat_1(X0,sK3)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4537,plain,
    ( ~ v1_partfun1(sK5,sK3)
    | ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2810])).

cnf(c_6009,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5508,c_43,c_37,c_36,c_35,c_2261,c_2313,c_2839,c_4537])).

cnf(c_6021,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6009,c_1769])).

cnf(c_2262,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2261])).

cnf(c_7487,plain,
    ( r1_xboole_0(X0,sK3) != iProver_top
    | k7_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6021,c_54,c_2262])).

cnf(c_7488,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7487])).

cnf(c_7495,plain,
    ( k7_relat_1(sK5,sK0(sK3)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1761,c_7488])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_772,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2269,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_2271,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2269])).

cnf(c_8503,plain,
    ( k7_relat_1(sK5,sK0(sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7495,c_42,c_2,c_2271])).

cnf(c_8506,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0(sK3)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8503,c_1766])).

cnf(c_8521,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK3)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8506,c_11])).

cnf(c_8906,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8521,c_54,c_2262])).

cnf(c_8911,plain,
    ( k9_relat_1(k7_relat_1(X0,sK0(sK3)),k1_xboole_0) = k9_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8906,c_1770])).

cnf(c_10898,plain,
    ( k9_relat_1(k7_relat_1(sK5,sK0(sK3)),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3005,c_8911])).

cnf(c_10900,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10898,c_7417,c_8503])).

cnf(c_3159,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_3005,c_1771])).

cnf(c_3655,plain,
    ( k9_relat_1(sK5,X0) != k1_xboole_0
    | k7_relat_1(sK5,X0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3159,c_1768])).

cnf(c_3672,plain,
    ( k9_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3655])).

cnf(c_2502,plain,
    ( v1_relat_1(k7_relat_1(sK5,X0))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2506,plain,
    ( v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_2508,plain,
    ( v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2506])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30989,c_28626,c_19733,c_10900,c_3672,c_2508,c_2262,c_54,c_53,c_52,c_50,c_48,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 8.02/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/1.48  
% 8.02/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.02/1.48  
% 8.02/1.48  ------  iProver source info
% 8.02/1.48  
% 8.02/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.02/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.02/1.48  git: non_committed_changes: false
% 8.02/1.48  git: last_make_outside_of_git: false
% 8.02/1.48  
% 8.02/1.48  ------ 
% 8.02/1.48  ------ Parsing...
% 8.02/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.02/1.48  
% 8.02/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 8.02/1.48  
% 8.02/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.02/1.48  
% 8.02/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.02/1.48  ------ Proving...
% 8.02/1.48  ------ Problem Properties 
% 8.02/1.48  
% 8.02/1.48  
% 8.02/1.48  clauses                                 44
% 8.02/1.48  conjectures                             14
% 8.02/1.48  EPR                                     12
% 8.02/1.48  Horn                                    34
% 8.02/1.48  unary                                   16
% 8.02/1.48  binary                                  10
% 8.02/1.48  lits                                    161
% 8.02/1.48  lits eq                                 25
% 8.02/1.48  fd_pure                                 0
% 8.02/1.48  fd_pseudo                               0
% 8.02/1.48  fd_cond                                 3
% 8.02/1.48  fd_pseudo_cond                          1
% 8.02/1.48  AC symbols                              0
% 8.02/1.48  
% 8.02/1.48  ------ Input Options Time Limit: Unbounded
% 8.02/1.48  
% 8.02/1.48  
% 8.02/1.48  ------ 
% 8.02/1.48  Current options:
% 8.02/1.48  ------ 
% 8.02/1.48  
% 8.02/1.48  
% 8.02/1.48  
% 8.02/1.48  
% 8.02/1.48  ------ Proving...
% 8.02/1.48  
% 8.02/1.48  
% 8.02/1.48  % SZS status Theorem for theBenchmark.p
% 8.02/1.48  
% 8.02/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.02/1.48  
% 8.02/1.48  fof(f23,conjecture,(
% 8.02/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f24,negated_conjecture,(
% 8.02/1.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 8.02/1.48    inference(negated_conjecture,[],[f23])).
% 8.02/1.48  
% 8.02/1.48  fof(f52,plain,(
% 8.02/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 8.02/1.48    inference(ennf_transformation,[],[f24])).
% 8.02/1.48  
% 8.02/1.48  fof(f53,plain,(
% 8.02/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 8.02/1.48    inference(flattening,[],[f52])).
% 8.02/1.48  
% 8.02/1.48  fof(f66,plain,(
% 8.02/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 8.02/1.48    introduced(choice_axiom,[])).
% 8.02/1.48  
% 8.02/1.48  fof(f65,plain,(
% 8.02/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 8.02/1.48    introduced(choice_axiom,[])).
% 8.02/1.48  
% 8.02/1.48  fof(f64,plain,(
% 8.02/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 8.02/1.48    introduced(choice_axiom,[])).
% 8.02/1.48  
% 8.02/1.48  fof(f63,plain,(
% 8.02/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 8.02/1.48    introduced(choice_axiom,[])).
% 8.02/1.48  
% 8.02/1.48  fof(f62,plain,(
% 8.02/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 8.02/1.48    introduced(choice_axiom,[])).
% 8.02/1.48  
% 8.02/1.48  fof(f61,plain,(
% 8.02/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 8.02/1.48    introduced(choice_axiom,[])).
% 8.02/1.48  
% 8.02/1.48  fof(f67,plain,(
% 8.02/1.48    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 8.02/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f53,f66,f65,f64,f63,f62,f61])).
% 8.02/1.48  
% 8.02/1.48  fof(f105,plain,(
% 8.02/1.48    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f3,axiom,(
% 8.02/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f27,plain,(
% 8.02/1.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.02/1.48    inference(ennf_transformation,[],[f3])).
% 8.02/1.48  
% 8.02/1.48  fof(f71,plain,(
% 8.02/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.02/1.48    inference(cnf_transformation,[],[f27])).
% 8.02/1.48  
% 8.02/1.48  fof(f5,axiom,(
% 8.02/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f73,plain,(
% 8.02/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 8.02/1.48    inference(cnf_transformation,[],[f5])).
% 8.02/1.48  
% 8.02/1.48  fof(f116,plain,(
% 8.02/1.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.02/1.48    inference(definition_unfolding,[],[f71,f73])).
% 8.02/1.48  
% 8.02/1.48  fof(f112,plain,(
% 8.02/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f20,axiom,(
% 8.02/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f46,plain,(
% 8.02/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 8.02/1.48    inference(ennf_transformation,[],[f20])).
% 8.02/1.48  
% 8.02/1.48  fof(f47,plain,(
% 8.02/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 8.02/1.48    inference(flattening,[],[f46])).
% 8.02/1.48  
% 8.02/1.48  fof(f93,plain,(
% 8.02/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f47])).
% 8.02/1.48  
% 8.02/1.48  fof(f110,plain,(
% 8.02/1.48    v1_funct_1(sK6)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f109,plain,(
% 8.02/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f107,plain,(
% 8.02/1.48    v1_funct_1(sK5)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f21,axiom,(
% 8.02/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f48,plain,(
% 8.02/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 8.02/1.48    inference(ennf_transformation,[],[f21])).
% 8.02/1.48  
% 8.02/1.48  fof(f49,plain,(
% 8.02/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 8.02/1.48    inference(flattening,[],[f48])).
% 8.02/1.48  
% 8.02/1.48  fof(f59,plain,(
% 8.02/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 8.02/1.48    inference(nnf_transformation,[],[f49])).
% 8.02/1.48  
% 8.02/1.48  fof(f60,plain,(
% 8.02/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 8.02/1.48    inference(flattening,[],[f59])).
% 8.02/1.48  
% 8.02/1.48  fof(f94,plain,(
% 8.02/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f60])).
% 8.02/1.48  
% 8.02/1.48  fof(f121,plain,(
% 8.02/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.02/1.48    inference(equality_resolution,[],[f94])).
% 8.02/1.48  
% 8.02/1.48  fof(f22,axiom,(
% 8.02/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f50,plain,(
% 8.02/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 8.02/1.48    inference(ennf_transformation,[],[f22])).
% 8.02/1.48  
% 8.02/1.48  fof(f51,plain,(
% 8.02/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 8.02/1.48    inference(flattening,[],[f50])).
% 8.02/1.48  
% 8.02/1.48  fof(f97,plain,(
% 8.02/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f51])).
% 8.02/1.48  
% 8.02/1.48  fof(f98,plain,(
% 8.02/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f51])).
% 8.02/1.48  
% 8.02/1.48  fof(f99,plain,(
% 8.02/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f51])).
% 8.02/1.48  
% 8.02/1.48  fof(f4,axiom,(
% 8.02/1.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f28,plain,(
% 8.02/1.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 8.02/1.48    inference(ennf_transformation,[],[f4])).
% 8.02/1.48  
% 8.02/1.48  fof(f72,plain,(
% 8.02/1.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f28])).
% 8.02/1.48  
% 8.02/1.48  fof(f101,plain,(
% 8.02/1.48    ~v1_xboole_0(sK2)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f102,plain,(
% 8.02/1.48    ~v1_xboole_0(sK3)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f108,plain,(
% 8.02/1.48    v1_funct_2(sK5,sK3,sK2)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f104,plain,(
% 8.02/1.48    ~v1_xboole_0(sK4)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f111,plain,(
% 8.02/1.48    v1_funct_2(sK6,sK4,sK2)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f106,plain,(
% 8.02/1.48    r1_subset_1(sK3,sK4)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f14,axiom,(
% 8.02/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f37,plain,(
% 8.02/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 8.02/1.48    inference(ennf_transformation,[],[f14])).
% 8.02/1.48  
% 8.02/1.48  fof(f38,plain,(
% 8.02/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 8.02/1.48    inference(flattening,[],[f37])).
% 8.02/1.48  
% 8.02/1.48  fof(f55,plain,(
% 8.02/1.48    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 8.02/1.48    inference(nnf_transformation,[],[f38])).
% 8.02/1.48  
% 8.02/1.48  fof(f84,plain,(
% 8.02/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f55])).
% 8.02/1.48  
% 8.02/1.48  fof(f1,axiom,(
% 8.02/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f54,plain,(
% 8.02/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 8.02/1.48    inference(nnf_transformation,[],[f1])).
% 8.02/1.48  
% 8.02/1.48  fof(f68,plain,(
% 8.02/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f54])).
% 8.02/1.48  
% 8.02/1.48  fof(f115,plain,(
% 8.02/1.48    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 8.02/1.48    inference(definition_unfolding,[],[f68,f73])).
% 8.02/1.48  
% 8.02/1.48  fof(f15,axiom,(
% 8.02/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f39,plain,(
% 8.02/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.02/1.48    inference(ennf_transformation,[],[f15])).
% 8.02/1.48  
% 8.02/1.48  fof(f86,plain,(
% 8.02/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.02/1.48    inference(cnf_transformation,[],[f39])).
% 8.02/1.48  
% 8.02/1.48  fof(f18,axiom,(
% 8.02/1.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f42,plain,(
% 8.02/1.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.02/1.48    inference(ennf_transformation,[],[f18])).
% 8.02/1.48  
% 8.02/1.48  fof(f43,plain,(
% 8.02/1.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.02/1.48    inference(flattening,[],[f42])).
% 8.02/1.48  
% 8.02/1.48  fof(f90,plain,(
% 8.02/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f43])).
% 8.02/1.48  
% 8.02/1.48  fof(f19,axiom,(
% 8.02/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f44,plain,(
% 8.02/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 8.02/1.48    inference(ennf_transformation,[],[f19])).
% 8.02/1.48  
% 8.02/1.48  fof(f45,plain,(
% 8.02/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.02/1.48    inference(flattening,[],[f44])).
% 8.02/1.48  
% 8.02/1.48  fof(f58,plain,(
% 8.02/1.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.02/1.48    inference(nnf_transformation,[],[f45])).
% 8.02/1.48  
% 8.02/1.48  fof(f91,plain,(
% 8.02/1.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f58])).
% 8.02/1.48  
% 8.02/1.48  fof(f16,axiom,(
% 8.02/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f26,plain,(
% 8.02/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 8.02/1.48    inference(pure_predicate_removal,[],[f16])).
% 8.02/1.48  
% 8.02/1.48  fof(f40,plain,(
% 8.02/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.02/1.48    inference(ennf_transformation,[],[f26])).
% 8.02/1.48  
% 8.02/1.48  fof(f87,plain,(
% 8.02/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.02/1.48    inference(cnf_transformation,[],[f40])).
% 8.02/1.48  
% 8.02/1.48  fof(f10,axiom,(
% 8.02/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f33,plain,(
% 8.02/1.48    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 8.02/1.48    inference(ennf_transformation,[],[f10])).
% 8.02/1.48  
% 8.02/1.48  fof(f78,plain,(
% 8.02/1.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f33])).
% 8.02/1.48  
% 8.02/1.48  fof(f13,axiom,(
% 8.02/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f36,plain,(
% 8.02/1.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 8.02/1.48    inference(ennf_transformation,[],[f13])).
% 8.02/1.48  
% 8.02/1.48  fof(f83,plain,(
% 8.02/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f36])).
% 8.02/1.48  
% 8.02/1.48  fof(f11,axiom,(
% 8.02/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f79,plain,(
% 8.02/1.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 8.02/1.48    inference(cnf_transformation,[],[f11])).
% 8.02/1.48  
% 8.02/1.48  fof(f9,axiom,(
% 8.02/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f32,plain,(
% 8.02/1.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 8.02/1.48    inference(ennf_transformation,[],[f9])).
% 8.02/1.48  
% 8.02/1.48  fof(f77,plain,(
% 8.02/1.48    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f32])).
% 8.02/1.48  
% 8.02/1.48  fof(f6,axiom,(
% 8.02/1.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f29,plain,(
% 8.02/1.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 8.02/1.48    inference(ennf_transformation,[],[f6])).
% 8.02/1.48  
% 8.02/1.48  fof(f74,plain,(
% 8.02/1.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f29])).
% 8.02/1.48  
% 8.02/1.48  fof(f7,axiom,(
% 8.02/1.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f30,plain,(
% 8.02/1.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 8.02/1.48    inference(ennf_transformation,[],[f7])).
% 8.02/1.48  
% 8.02/1.48  fof(f75,plain,(
% 8.02/1.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f30])).
% 8.02/1.48  
% 8.02/1.48  fof(f80,plain,(
% 8.02/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 8.02/1.48    inference(cnf_transformation,[],[f11])).
% 8.02/1.48  
% 8.02/1.48  fof(f8,axiom,(
% 8.02/1.48    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f31,plain,(
% 8.02/1.48    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 8.02/1.48    inference(ennf_transformation,[],[f8])).
% 8.02/1.48  
% 8.02/1.48  fof(f76,plain,(
% 8.02/1.48    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f31])).
% 8.02/1.48  
% 8.02/1.48  fof(f12,axiom,(
% 8.02/1.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f34,plain,(
% 8.02/1.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 8.02/1.48    inference(ennf_transformation,[],[f12])).
% 8.02/1.48  
% 8.02/1.48  fof(f35,plain,(
% 8.02/1.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.02/1.48    inference(flattening,[],[f34])).
% 8.02/1.48  
% 8.02/1.48  fof(f82,plain,(
% 8.02/1.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f35])).
% 8.02/1.48  
% 8.02/1.48  fof(f100,plain,(
% 8.02/1.48    ~v1_xboole_0(sK1)),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f103,plain,(
% 8.02/1.48    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f95,plain,(
% 8.02/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.02/1.48    inference(cnf_transformation,[],[f60])).
% 8.02/1.48  
% 8.02/1.48  fof(f120,plain,(
% 8.02/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.02/1.48    inference(equality_resolution,[],[f95])).
% 8.02/1.48  
% 8.02/1.48  fof(f113,plain,(
% 8.02/1.48    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 8.02/1.48    inference(cnf_transformation,[],[f67])).
% 8.02/1.48  
% 8.02/1.48  fof(f17,axiom,(
% 8.02/1.48    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f25,plain,(
% 8.02/1.48    ! [X0] : ~(! [X1] : ~r1_xboole_0(X1,X0) & k1_xboole_0 != X0)),
% 8.02/1.48    inference(pure_predicate_removal,[],[f17])).
% 8.02/1.48  
% 8.02/1.48  fof(f41,plain,(
% 8.02/1.48    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) | k1_xboole_0 = X0)),
% 8.02/1.48    inference(ennf_transformation,[],[f25])).
% 8.02/1.48  
% 8.02/1.48  fof(f56,plain,(
% 8.02/1.48    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) => r1_xboole_0(sK0(X0),X0))),
% 8.02/1.48    introduced(choice_axiom,[])).
% 8.02/1.48  
% 8.02/1.48  fof(f57,plain,(
% 8.02/1.48    ! [X0] : (r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0)),
% 8.02/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f56])).
% 8.02/1.48  
% 8.02/1.48  fof(f88,plain,(
% 8.02/1.48    ( ! [X0] : (r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 8.02/1.48    inference(cnf_transformation,[],[f57])).
% 8.02/1.48  
% 8.02/1.48  fof(f2,axiom,(
% 8.02/1.48    v1_xboole_0(k1_xboole_0)),
% 8.02/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.48  
% 8.02/1.48  fof(f70,plain,(
% 8.02/1.48    v1_xboole_0(k1_xboole_0)),
% 8.02/1.48    inference(cnf_transformation,[],[f2])).
% 8.02/1.48  
% 8.02/1.48  cnf(c_39,negated_conjecture,
% 8.02/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 8.02/1.48      inference(cnf_transformation,[],[f105]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1745,plain,
% 8.02/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3,plain,
% 8.02/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.02/1.48      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 8.02/1.48      inference(cnf_transformation,[],[f116]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1775,plain,
% 8.02/1.48      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3679,plain,
% 8.02/1.48      ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1745,c_1775]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_32,negated_conjecture,
% 8.02/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 8.02/1.48      inference(cnf_transformation,[],[f112]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1752,plain,
% 8.02/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_24,plain,
% 8.02/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 8.02/1.48      inference(cnf_transformation,[],[f93]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1757,plain,
% 8.02/1.48      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.02/1.48      | v1_funct_1(X2) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5527,plain,
% 8.02/1.48      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 8.02/1.48      | v1_funct_1(sK6) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1752,c_1757]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_34,negated_conjecture,
% 8.02/1.48      ( v1_funct_1(sK6) ),
% 8.02/1.48      inference(cnf_transformation,[],[f110]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2400,plain,
% 8.02/1.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.02/1.48      | ~ v1_funct_1(sK6)
% 8.02/1.48      | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_24]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2842,plain,
% 8.02/1.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 8.02/1.48      | ~ v1_funct_1(sK6)
% 8.02/1.48      | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2400]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5783,plain,
% 8.02/1.48      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_5527,c_34,c_32,c_2842]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_35,negated_conjecture,
% 8.02/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 8.02/1.48      inference(cnf_transformation,[],[f109]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1749,plain,
% 8.02/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5528,plain,
% 8.02/1.48      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 8.02/1.48      | v1_funct_1(sK5) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1749,c_1757]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_37,negated_conjecture,
% 8.02/1.48      ( v1_funct_1(sK5) ),
% 8.02/1.48      inference(cnf_transformation,[],[f107]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2405,plain,
% 8.02/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_24]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2847,plain,
% 8.02/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2405]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5789,plain,
% 8.02/1.48      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_5528,c_37,c_35,c_2847]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_27,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(X3)
% 8.02/1.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 8.02/1.48      inference(cnf_transformation,[],[f121]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(X3)
% 8.02/1.48      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X1) ),
% 8.02/1.48      inference(cnf_transformation,[],[f97]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_29,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(X3)
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X1) ),
% 8.02/1.48      inference(cnf_transformation,[],[f98]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_28,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(X3)
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X1) ),
% 8.02/1.48      inference(cnf_transformation,[],[f99]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_442,plain,
% 8.02/1.48      ( ~ v1_funct_1(X3)
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_27,c_30,c_29,c_28]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_443,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(X3)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_442]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1739,plain,
% 8.02/1.48      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 8.02/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.02/1.48      | v1_funct_2(X5,X4,X1) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.02/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 8.02/1.48      | v1_funct_1(X2) != iProver_top
% 8.02/1.48      | v1_funct_1(X5) != iProver_top
% 8.02/1.48      | v1_xboole_0(X3) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(X4) = iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4,plain,
% 8.02/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.02/1.48      | ~ v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(X0) ),
% 8.02/1.48      inference(cnf_transformation,[],[f72]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1774,plain,
% 8.02/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.02/1.48      | v1_xboole_0(X1) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2053,plain,
% 8.02/1.48      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
% 8.02/1.48      | v1_funct_2(X5,X4,X1) != iProver_top
% 8.02/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 8.02/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.02/1.48      | v1_funct_1(X5) != iProver_top
% 8.02/1.48      | v1_funct_1(X2) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(X4) = iProver_top ),
% 8.02/1.48      inference(forward_subsumption_resolution,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_1739,c_1774]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_12072,plain,
% 8.02/1.48      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | v1_funct_1(X1) != iProver_top
% 8.02/1.48      | v1_funct_1(sK5) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK2) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_5789,c_2053]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_43,negated_conjecture,
% 8.02/1.48      ( ~ v1_xboole_0(sK2) ),
% 8.02/1.48      inference(cnf_transformation,[],[f101]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_46,plain,
% 8.02/1.48      ( v1_xboole_0(sK2) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_42,negated_conjecture,
% 8.02/1.48      ( ~ v1_xboole_0(sK3) ),
% 8.02/1.48      inference(cnf_transformation,[],[f102]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_47,plain,
% 8.02/1.48      ( v1_xboole_0(sK3) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_52,plain,
% 8.02/1.48      ( v1_funct_1(sK5) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_36,negated_conjecture,
% 8.02/1.48      ( v1_funct_2(sK5,sK3,sK2) ),
% 8.02/1.48      inference(cnf_transformation,[],[f108]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_53,plain,
% 8.02/1.48      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_54,plain,
% 8.02/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30541,plain,
% 8.02/1.48      ( v1_funct_1(X1) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 8.02/1.48      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_12072,c_46,c_47,c_52,c_53,c_54]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30542,plain,
% 8.02/1.48      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | v1_funct_1(X1) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_30541]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30553,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 8.02/1.48      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 8.02/1.48      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | v1_funct_1(sK6) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK4) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_5783,c_30542]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_40,negated_conjecture,
% 8.02/1.48      ( ~ v1_xboole_0(sK4) ),
% 8.02/1.48      inference(cnf_transformation,[],[f104]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_49,plain,
% 8.02/1.48      ( v1_xboole_0(sK4) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_55,plain,
% 8.02/1.48      ( v1_funct_1(sK6) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_33,negated_conjecture,
% 8.02/1.48      ( v1_funct_2(sK6,sK4,sK2) ),
% 8.02/1.48      inference(cnf_transformation,[],[f111]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_56,plain,
% 8.02/1.48      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_57,plain,
% 8.02/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30976,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 8.02/1.48      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_30553,c_49,c_55,c_56,c_57]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30986,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 8.02/1.48      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3679,c_30976]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_38,negated_conjecture,
% 8.02/1.48      ( r1_subset_1(sK3,sK4) ),
% 8.02/1.48      inference(cnf_transformation,[],[f106]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1746,plain,
% 8.02/1.48      ( r1_subset_1(sK3,sK4) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_16,plain,
% 8.02/1.48      ( ~ r1_subset_1(X0,X1)
% 8.02/1.48      | r1_xboole_0(X0,X1)
% 8.02/1.48      | v1_xboole_0(X0)
% 8.02/1.48      | v1_xboole_0(X1) ),
% 8.02/1.48      inference(cnf_transformation,[],[f84]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1764,plain,
% 8.02/1.48      ( r1_subset_1(X0,X1) != iProver_top
% 8.02/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4317,plain,
% 8.02/1.48      ( r1_xboole_0(sK3,sK4) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK4) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1746,c_1764]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_51,plain,
% 8.02/1.48      ( r1_subset_1(sK3,sK4) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2316,plain,
% 8.02/1.48      ( ~ r1_subset_1(sK3,sK4)
% 8.02/1.48      | r1_xboole_0(sK3,sK4)
% 8.02/1.48      | v1_xboole_0(sK4)
% 8.02/1.48      | v1_xboole_0(sK3) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2317,plain,
% 8.02/1.48      ( r1_subset_1(sK3,sK4) != iProver_top
% 8.02/1.48      | r1_xboole_0(sK3,sK4) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK4) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_2316]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4693,plain,
% 8.02/1.48      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_4317,c_47,c_49,c_51,c_2317]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1,plain,
% 8.02/1.48      ( ~ r1_xboole_0(X0,X1)
% 8.02/1.48      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 8.02/1.48      inference(cnf_transformation,[],[f115]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1777,plain,
% 8.02/1.48      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 8.02/1.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4698,plain,
% 8.02/1.48      ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_4693,c_1777]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_17,plain,
% 8.02/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | v1_relat_1(X0) ),
% 8.02/1.48      inference(cnf_transformation,[],[f86]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1763,plain,
% 8.02/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.02/1.48      | v1_relat_1(X0) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3004,plain,
% 8.02/1.48      ( v1_relat_1(sK6) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1752,c_1763]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_20,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | v1_partfun1(X0,X1)
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | v1_xboole_0(X2) ),
% 8.02/1.48      inference(cnf_transformation,[],[f90]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1760,plain,
% 8.02/1.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 8.02/1.48      | v1_partfun1(X0,X1) = iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.02/1.48      | v1_funct_1(X0) != iProver_top
% 8.02/1.48      | v1_xboole_0(X2) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2955,plain,
% 8.02/1.48      ( v1_funct_2(sK6,sK4,sK2) != iProver_top
% 8.02/1.48      | v1_partfun1(sK6,sK4) = iProver_top
% 8.02/1.48      | v1_funct_1(sK6) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1752,c_1760]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2394,plain,
% 8.02/1.48      ( ~ v1_funct_2(sK6,X0,X1)
% 8.02/1.48      | v1_partfun1(sK6,X0)
% 8.02/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.02/1.48      | ~ v1_funct_1(sK6)
% 8.02/1.48      | v1_xboole_0(X1) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2836,plain,
% 8.02/1.48      ( ~ v1_funct_2(sK6,sK4,sK2)
% 8.02/1.48      | v1_partfun1(sK6,sK4)
% 8.02/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 8.02/1.48      | ~ v1_funct_1(sK6)
% 8.02/1.48      | v1_xboole_0(sK2) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2394]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2837,plain,
% 8.02/1.48      ( v1_funct_2(sK6,sK4,sK2) != iProver_top
% 8.02/1.48      | v1_partfun1(sK6,sK4) = iProver_top
% 8.02/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 8.02/1.48      | v1_funct_1(sK6) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_2836]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3231,plain,
% 8.02/1.48      ( v1_partfun1(sK6,sK4) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_2955,c_46,c_55,c_56,c_57,c_2837]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_23,plain,
% 8.02/1.48      ( ~ v1_partfun1(X0,X1)
% 8.02/1.48      | ~ v4_relat_1(X0,X1)
% 8.02/1.48      | ~ v1_relat_1(X0)
% 8.02/1.48      | k1_relat_1(X0) = X1 ),
% 8.02/1.48      inference(cnf_transformation,[],[f91]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1758,plain,
% 8.02/1.48      ( k1_relat_1(X0) = X1
% 8.02/1.48      | v1_partfun1(X0,X1) != iProver_top
% 8.02/1.48      | v4_relat_1(X0,X1) != iProver_top
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5507,plain,
% 8.02/1.48      ( k1_relat_1(sK6) = sK4
% 8.02/1.48      | v4_relat_1(sK6,sK4) != iProver_top
% 8.02/1.48      | v1_relat_1(sK6) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3231,c_1758]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2258,plain,
% 8.02/1.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 8.02/1.48      | v1_relat_1(sK6) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_18,plain,
% 8.02/1.48      ( v4_relat_1(X0,X1)
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 8.02/1.48      inference(cnf_transformation,[],[f87]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2310,plain,
% 8.02/1.48      ( v4_relat_1(sK6,sK4)
% 8.02/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2757,plain,
% 8.02/1.48      ( ~ v1_partfun1(X0,sK4)
% 8.02/1.48      | ~ v4_relat_1(X0,sK4)
% 8.02/1.48      | ~ v1_relat_1(X0)
% 8.02/1.48      | k1_relat_1(X0) = sK4 ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4405,plain,
% 8.02/1.48      ( ~ v1_partfun1(sK6,sK4)
% 8.02/1.48      | ~ v4_relat_1(sK6,sK4)
% 8.02/1.48      | ~ v1_relat_1(sK6)
% 8.02/1.48      | k1_relat_1(sK6) = sK4 ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2757]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5974,plain,
% 8.02/1.48      ( k1_relat_1(sK6) = sK4 ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_5507,c_43,c_34,c_33,c_32,c_2258,c_2310,c_2836,c_4405]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_9,plain,
% 8.02/1.48      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 8.02/1.48      | ~ v1_relat_1(X1)
% 8.02/1.48      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 8.02/1.48      inference(cnf_transformation,[],[f78]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1769,plain,
% 8.02/1.48      ( k7_relat_1(X0,X1) = k1_xboole_0
% 8.02/1.48      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5986,plain,
% 8.02/1.48      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 8.02/1.48      | r1_xboole_0(X0,sK4) != iProver_top
% 8.02/1.48      | v1_relat_1(sK6) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_5974,c_1769]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2259,plain,
% 8.02/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 8.02/1.48      | v1_relat_1(sK6) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_2258]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7164,plain,
% 8.02/1.48      ( r1_xboole_0(X0,sK4) != iProver_top
% 8.02/1.48      | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_5986,c_57,c_2259]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7165,plain,
% 8.02/1.48      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 8.02/1.48      | r1_xboole_0(X0,sK4) != iProver_top ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_7164]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7173,plain,
% 8.02/1.48      ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_4693,c_7165]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_14,plain,
% 8.02/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 8.02/1.48      inference(cnf_transformation,[],[f83]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1766,plain,
% 8.02/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7181,plain,
% 8.02/1.48      ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
% 8.02/1.48      | v1_relat_1(sK6) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_7173,c_1766]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_11,plain,
% 8.02/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 8.02/1.48      inference(cnf_transformation,[],[f79]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7197,plain,
% 8.02/1.48      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 8.02/1.48      | v1_relat_1(sK6) != iProver_top ),
% 8.02/1.48      inference(light_normalisation,[status(thm)],[c_7181,c_11]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7807,plain,
% 8.02/1.48      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_7197,c_57,c_2259]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_8,plain,
% 8.02/1.48      ( ~ r1_tarski(X0,X1)
% 8.02/1.48      | ~ v1_relat_1(X2)
% 8.02/1.48      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 8.02/1.48      inference(cnf_transformation,[],[f77]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1770,plain,
% 8.02/1.48      ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 8.02/1.48      | r1_tarski(X2,X1) != iProver_top
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7812,plain,
% 8.02/1.48      ( k9_relat_1(k7_relat_1(X0,sK3),k1_xboole_0) = k9_relat_1(X0,k1_xboole_0)
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_7807,c_1770]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_9032,plain,
% 8.02/1.48      ( k9_relat_1(k7_relat_1(sK6,sK3),k1_xboole_0) = k9_relat_1(sK6,k1_xboole_0) ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3004,c_7812]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5,plain,
% 8.02/1.48      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 8.02/1.48      inference(cnf_transformation,[],[f74]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1773,plain,
% 8.02/1.48      ( v1_relat_1(X0) != iProver_top
% 8.02/1.48      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7182,plain,
% 8.02/1.48      ( v1_relat_1(sK6) != iProver_top
% 8.02/1.48      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_7173,c_1773]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7408,plain,
% 8.02/1.48      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_7182,c_57,c_2259]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_6,plain,
% 8.02/1.48      ( ~ v1_relat_1(X0)
% 8.02/1.48      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 8.02/1.48      inference(cnf_transformation,[],[f75]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1772,plain,
% 8.02/1.48      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7415,plain,
% 8.02/1.48      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_7408,c_1772]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_10,plain,
% 8.02/1.48      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 8.02/1.48      inference(cnf_transformation,[],[f80]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7417,plain,
% 8.02/1.48      ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 8.02/1.48      inference(light_normalisation,[status(thm)],[c_7415,c_10,c_11]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_9037,plain,
% 8.02/1.48      ( k9_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 8.02/1.48      inference(light_normalisation,[status(thm)],[c_9032,c_7173,c_7417]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7,plain,
% 8.02/1.48      ( ~ v1_relat_1(X0)
% 8.02/1.48      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 8.02/1.48      inference(cnf_transformation,[],[f76]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1771,plain,
% 8.02/1.48      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3150,plain,
% 8.02/1.48      ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3004,c_1771]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_12,plain,
% 8.02/1.48      ( ~ v1_relat_1(X0)
% 8.02/1.48      | k2_relat_1(X0) != k1_xboole_0
% 8.02/1.48      | k1_xboole_0 = X0 ),
% 8.02/1.48      inference(cnf_transformation,[],[f82]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1768,plain,
% 8.02/1.48      ( k2_relat_1(X0) != k1_xboole_0
% 8.02/1.48      | k1_xboole_0 = X0
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3654,plain,
% 8.02/1.48      ( k9_relat_1(sK6,X0) != k1_xboole_0
% 8.02/1.48      | k7_relat_1(sK6,X0) = k1_xboole_0
% 8.02/1.48      | v1_relat_1(k7_relat_1(sK6,X0)) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3150,c_1768]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2474,plain,
% 8.02/1.48      ( v1_relat_1(k7_relat_1(sK6,X0)) | ~ v1_relat_1(sK6) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3668,plain,
% 8.02/1.48      ( ~ v1_relat_1(k7_relat_1(sK6,X0))
% 8.02/1.48      | k9_relat_1(sK6,X0) != k1_xboole_0
% 8.02/1.48      | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 8.02/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_3654]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4199,plain,
% 8.02/1.48      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 8.02/1.48      | k9_relat_1(sK6,X0) != k1_xboole_0 ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_3654,c_32,c_2258,c_2474,c_3668]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4200,plain,
% 8.02/1.48      ( k9_relat_1(sK6,X0) != k1_xboole_0
% 8.02/1.48      | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_4199]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_9083,plain,
% 8.02/1.48      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_9037,c_4200]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30987,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 8.02/1.48      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 8.02/1.48      inference(light_normalisation,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_30986,c_4698,c_9083]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1755,plain,
% 8.02/1.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 8.02/1.48      | v1_funct_2(X3,X4,X2) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.02/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 8.02/1.48      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
% 8.02/1.48      | v1_funct_1(X0) != iProver_top
% 8.02/1.48      | v1_funct_1(X3) != iProver_top
% 8.02/1.48      | v1_xboole_0(X5) = iProver_top
% 8.02/1.48      | v1_xboole_0(X2) = iProver_top
% 8.02/1.48      | v1_xboole_0(X4) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1998,plain,
% 8.02/1.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 8.02/1.48      | v1_funct_2(X3,X4,X2) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.02/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 8.02/1.48      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
% 8.02/1.48      | v1_funct_1(X0) != iProver_top
% 8.02/1.48      | v1_funct_1(X3) != iProver_top
% 8.02/1.48      | v1_xboole_0(X2) = iProver_top
% 8.02/1.48      | v1_xboole_0(X4) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top ),
% 8.02/1.48      inference(forward_subsumption_resolution,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_1755,c_1774]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_8540,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 8.02/1.48      | v1_funct_2(X5,X2,X3) != iProver_top
% 8.02/1.48      | v1_funct_2(X4,X1,X3) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 8.02/1.48      | v1_funct_1(X5) != iProver_top
% 8.02/1.48      | v1_funct_1(X4) != iProver_top
% 8.02/1.48      | v1_funct_1(k1_tmap_1(X0,X3,X1,X2,X4,X5)) != iProver_top
% 8.02/1.48      | v1_xboole_0(X3) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(X2) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1998,c_1757]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1753,plain,
% 8.02/1.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 8.02/1.48      | v1_funct_2(X3,X4,X2) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.02/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 8.02/1.48      | v1_funct_1(X0) != iProver_top
% 8.02/1.48      | v1_funct_1(X3) != iProver_top
% 8.02/1.48      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 8.02/1.48      | v1_xboole_0(X5) = iProver_top
% 8.02/1.48      | v1_xboole_0(X2) = iProver_top
% 8.02/1.48      | v1_xboole_0(X4) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1946,plain,
% 8.02/1.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 8.02/1.48      | v1_funct_2(X3,X4,X2) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.02/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 8.02/1.48      | v1_funct_1(X0) != iProver_top
% 8.02/1.48      | v1_funct_1(X3) != iProver_top
% 8.02/1.48      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 8.02/1.48      | v1_xboole_0(X2) = iProver_top
% 8.02/1.48      | v1_xboole_0(X4) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top ),
% 8.02/1.48      inference(forward_subsumption_resolution,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_1753,c_1774]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19033,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 8.02/1.48      | v1_funct_2(X5,X2,X3) != iProver_top
% 8.02/1.48      | v1_funct_2(X4,X1,X3) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 8.02/1.48      | v1_funct_1(X5) != iProver_top
% 8.02/1.48      | v1_funct_1(X4) != iProver_top
% 8.02/1.48      | v1_xboole_0(X2) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(X3) = iProver_top ),
% 8.02/1.48      inference(forward_subsumption_resolution,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_8540,c_1946]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19036,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 8.02/1.48      | v1_funct_2(X2,X1,sK2) != iProver_top
% 8.02/1.48      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | v1_funct_1(X2) != iProver_top
% 8.02/1.48      | v1_funct_1(sK6) != iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK2) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK4) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1752,c_19033]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19321,plain,
% 8.02/1.48      ( v1_funct_1(X2) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 8.02/1.48      | v1_funct_2(X2,X1,sK2) != iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_19036,c_46,c_49,c_55,c_56]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19322,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 8.02/1.48      | v1_funct_2(X2,X1,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | v1_funct_1(X2) != iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_19321]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19334,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
% 8.02/1.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | v1_funct_1(sK5) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1749,c_19322]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19714,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_19334,c_47,c_52,c_53]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19723,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0)
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1745,c_19714]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_44,negated_conjecture,
% 8.02/1.48      ( ~ v1_xboole_0(sK1) ),
% 8.02/1.48      inference(cnf_transformation,[],[f100]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_41,negated_conjecture,
% 8.02/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 8.02/1.48      inference(cnf_transformation,[],[f103]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2450,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(sK5,X3,X2)
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | m1_subset_1(k1_tmap_1(X4,X2,X3,X1,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X3,X1),X2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X3)
% 8.02/1.48      | v1_xboole_0(X4) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_28]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2916,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,sK2)
% 8.02/1.48      | ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 8.02/1.48      | m1_subset_1(k1_tmap_1(X2,sK2,sK3,X1,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,sK3,X1),sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(sK2)
% 8.02/1.48      | v1_xboole_0(sK3) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2450]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3289,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,sK2)
% 8.02/1.48      | ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
% 8.02/1.48      | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X1,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X1),sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(sK2)
% 8.02/1.48      | v1_xboole_0(sK3)
% 8.02/1.48      | v1_xboole_0(sK1) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2916]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3895,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,sK4,sK2)
% 8.02/1.48      | ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 8.02/1.48      | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 8.02/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(sK2)
% 8.02/1.48      | v1_xboole_0(sK4)
% 8.02/1.48      | v1_xboole_0(sK3)
% 8.02/1.48      | v1_xboole_0(sK1) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_3289]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5472,plain,
% 8.02/1.48      ( ~ v1_funct_2(sK6,sK4,sK2)
% 8.02/1.48      | ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 8.02/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 8.02/1.48      | ~ v1_funct_1(sK6)
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(sK2)
% 8.02/1.48      | v1_xboole_0(sK4)
% 8.02/1.48      | v1_xboole_0(sK3)
% 8.02/1.48      | v1_xboole_0(sK1) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_3895]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_6865,plain,
% 8.02/1.48      ( ~ m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
% 8.02/1.48      | ~ v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_24]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2444,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(sK5,X3,X2)
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | v1_funct_1(k1_tmap_1(X4,X2,X3,X1,sK5,X0))
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X3)
% 8.02/1.48      | v1_xboole_0(X4) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_30]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2873,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,sK2)
% 8.02/1.48      | ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | v1_funct_1(k1_tmap_1(X2,sK2,sK3,X1,sK5,X0))
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(sK2)
% 8.02/1.48      | v1_xboole_0(sK3) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2444]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5884,plain,
% 8.02/1.48      ( ~ v1_funct_2(sK6,X0,sK2)
% 8.02/1.48      | ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.02/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
% 8.02/1.48      | v1_funct_1(k1_tmap_1(X1,sK2,sK3,X0,sK5,sK6))
% 8.02/1.48      | ~ v1_funct_1(sK6)
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(X0)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(sK2)
% 8.02/1.48      | v1_xboole_0(sK3) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2873]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7388,plain,
% 8.02/1.48      ( ~ v1_funct_2(sK6,sK4,sK2)
% 8.02/1.48      | ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 8.02/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 8.02/1.48      | v1_funct_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6))
% 8.02/1.48      | ~ v1_funct_1(sK6)
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(X0)
% 8.02/1.48      | v1_xboole_0(sK2)
% 8.02/1.48      | v1_xboole_0(sK4)
% 8.02/1.48      | v1_xboole_0(sK3) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_5884]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_11660,plain,
% 8.02/1.48      ( ~ v1_funct_2(sK6,sK4,sK2)
% 8.02/1.48      | ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 8.02/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 8.02/1.48      | v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
% 8.02/1.48      | ~ v1_funct_1(sK6)
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(sK2)
% 8.02/1.48      | v1_xboole_0(sK4)
% 8.02/1.48      | v1_xboole_0(sK3)
% 8.02/1.48      | v1_xboole_0(sK1) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_7388]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19728,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_19723,c_44,c_43,c_42,c_41,c_40,c_39,c_37,c_36,c_35,
% 8.02/1.48                 c_34,c_33,c_32,c_5472,c_6865,c_11660]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30988,plain,
% 8.02/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 8.02/1.48      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_30987,c_3679,c_19728]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_30989,plain,
% 8.02/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 8.02/1.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 8.02/1.48      inference(light_normalisation,[status(thm)],[c_30988,c_4698]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_26,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(X3)
% 8.02/1.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 8.02/1.48      inference(cnf_transformation,[],[f120]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_449,plain,
% 8.02/1.48      ( ~ v1_funct_1(X3)
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_26,c_30,c_29,c_28]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_450,plain,
% 8.02/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 8.02/1.48      | ~ v1_funct_2(X3,X4,X2)
% 8.02/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 8.02/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.02/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.02/1.48      | ~ v1_funct_1(X0)
% 8.02/1.48      | ~ v1_funct_1(X3)
% 8.02/1.48      | v1_xboole_0(X1)
% 8.02/1.48      | v1_xboole_0(X2)
% 8.02/1.48      | v1_xboole_0(X4)
% 8.02/1.48      | v1_xboole_0(X5)
% 8.02/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_449]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1738,plain,
% 8.02/1.48      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 8.02/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.02/1.48      | v1_funct_2(X5,X4,X1) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.02/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 8.02/1.48      | v1_funct_1(X2) != iProver_top
% 8.02/1.48      | v1_funct_1(X5) != iProver_top
% 8.02/1.48      | v1_xboole_0(X3) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(X4) = iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2025,plain,
% 8.02/1.48      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
% 8.02/1.48      | v1_funct_2(X5,X4,X1) != iProver_top
% 8.02/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 8.02/1.48      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 8.02/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 8.02/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.02/1.48      | v1_funct_1(X5) != iProver_top
% 8.02/1.48      | v1_funct_1(X2) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top
% 8.02/1.48      | v1_xboole_0(X1) = iProver_top
% 8.02/1.48      | v1_xboole_0(X4) = iProver_top ),
% 8.02/1.48      inference(forward_subsumption_resolution,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_1738,c_1774]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_9847,plain,
% 8.02/1.48      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | v1_funct_1(X1) != iProver_top
% 8.02/1.48      | v1_funct_1(sK6) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK2) = iProver_top
% 8.02/1.48      | v1_xboole_0(sK4) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_5783,c_2025]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_27897,plain,
% 8.02/1.48      ( v1_funct_1(X1) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 8.02/1.48      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_9847,c_46,c_49,c_55,c_56,c_57]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_27898,plain,
% 8.02/1.48      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 8.02/1.48      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 8.02/1.48      | v1_funct_1(X1) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_27897]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_27915,plain,
% 8.02/1.48      ( k2_partfun1(X0,sK2,X1,k1_setfam_1(k2_tarski(X0,sK4))) != k7_relat_1(sK6,k9_subset_1(sK1,X0,sK4))
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | v1_funct_1(X1) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3679,c_27898]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_27924,plain,
% 8.02/1.48      ( k2_partfun1(X0,sK2,X1,k1_setfam_1(k2_tarski(X0,sK4))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(X0,sK4)))
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | v1_funct_1(X1) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(light_normalisation,[status(thm)],[c_27915,c_3679]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_50,plain,
% 8.02/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_28512,plain,
% 8.02/1.48      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 8.02/1.48      | k2_partfun1(X0,sK2,X1,k1_setfam_1(k2_tarski(X0,sK4))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(X0,sK4)))
% 8.02/1.48      | v1_funct_1(X1) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_27924,c_50]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_28513,plain,
% 8.02/1.48      ( k2_partfun1(X0,sK2,X1,k1_setfam_1(k2_tarski(X0,sK4))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(X0,sK4)))
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,X0,sK4),sK2,k1_tmap_1(sK1,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 8.02/1.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | v1_funct_1(X1) != iProver_top
% 8.02/1.48      | v1_xboole_0(X0) = iProver_top ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_28512]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_28524,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 8.02/1.48      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4)))
% 8.02/1.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | v1_funct_1(sK5) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_5789,c_28513]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_28625,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 8.02/1.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 8.02/1.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | v1_funct_1(sK5) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 8.02/1.48      inference(light_normalisation,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_28524,c_4698,c_9083]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_28626,plain,
% 8.02/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 8.02/1.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 8.02/1.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 8.02/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.02/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 8.02/1.48      | v1_funct_1(sK5) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_28625,c_19728]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_31,negated_conjecture,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 8.02/1.48      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 8.02/1.48      inference(cnf_transformation,[],[f113]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3973,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 8.02/1.48      | k2_partfun1(sK4,sK2,sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k2_partfun1(sK3,sK2,sK5,k1_setfam_1(k2_tarski(sK3,sK4))) ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_3679,c_31]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4778,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 8.02/1.48      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_4698,c_3973]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5787,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 8.02/1.48      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_5783,c_4778]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_6116,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 8.02/1.48      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_5787,c_5789]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_9205,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 8.02/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 8.02/1.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_9083,c_6116]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19732,plain,
% 8.02/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 8.02/1.48      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 8.02/1.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_19728,c_9205]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19733,plain,
% 8.02/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 8.02/1.48      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 8.02/1.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 8.02/1.48      inference(demodulation,[status(thm)],[c_19732,c_19728]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3005,plain,
% 8.02/1.48      ( v1_relat_1(sK5) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1749,c_1763]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_19,plain,
% 8.02/1.48      ( r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 8.02/1.48      inference(cnf_transformation,[],[f88]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_1761,plain,
% 8.02/1.48      ( k1_xboole_0 = X0 | r1_xboole_0(sK0(X0),X0) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2956,plain,
% 8.02/1.48      ( v1_funct_2(sK5,sK3,sK2) != iProver_top
% 8.02/1.48      | v1_partfun1(sK5,sK3) = iProver_top
% 8.02/1.48      | v1_funct_1(sK5) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1749,c_1760]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2397,plain,
% 8.02/1.48      ( ~ v1_funct_2(sK5,X0,X1)
% 8.02/1.48      | v1_partfun1(sK5,X0)
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(X1) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2839,plain,
% 8.02/1.48      ( ~ v1_funct_2(sK5,sK3,sK2)
% 8.02/1.48      | v1_partfun1(sK5,sK3)
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | ~ v1_funct_1(sK5)
% 8.02/1.48      | v1_xboole_0(sK2) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2397]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2840,plain,
% 8.02/1.48      ( v1_funct_2(sK5,sK3,sK2) != iProver_top
% 8.02/1.48      | v1_partfun1(sK5,sK3) = iProver_top
% 8.02/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.02/1.48      | v1_funct_1(sK5) != iProver_top
% 8.02/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_2839]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3237,plain,
% 8.02/1.48      ( v1_partfun1(sK5,sK3) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_2956,c_46,c_52,c_53,c_54,c_2840]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_5508,plain,
% 8.02/1.48      ( k1_relat_1(sK5) = sK3
% 8.02/1.48      | v4_relat_1(sK5,sK3) != iProver_top
% 8.02/1.48      | v1_relat_1(sK5) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3237,c_1758]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2261,plain,
% 8.02/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.02/1.48      | v1_relat_1(sK5) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2313,plain,
% 8.02/1.48      ( v4_relat_1(sK5,sK3)
% 8.02/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2810,plain,
% 8.02/1.48      ( ~ v1_partfun1(X0,sK3)
% 8.02/1.48      | ~ v4_relat_1(X0,sK3)
% 8.02/1.48      | ~ v1_relat_1(X0)
% 8.02/1.48      | k1_relat_1(X0) = sK3 ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_4537,plain,
% 8.02/1.48      ( ~ v1_partfun1(sK5,sK3)
% 8.02/1.48      | ~ v4_relat_1(sK5,sK3)
% 8.02/1.48      | ~ v1_relat_1(sK5)
% 8.02/1.48      | k1_relat_1(sK5) = sK3 ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2810]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_6009,plain,
% 8.02/1.48      ( k1_relat_1(sK5) = sK3 ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_5508,c_43,c_37,c_36,c_35,c_2261,c_2313,c_2839,c_4537]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_6021,plain,
% 8.02/1.48      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 8.02/1.48      | r1_xboole_0(X0,sK3) != iProver_top
% 8.02/1.48      | v1_relat_1(sK5) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_6009,c_1769]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2262,plain,
% 8.02/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.02/1.48      | v1_relat_1(sK5) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_2261]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7487,plain,
% 8.02/1.48      ( r1_xboole_0(X0,sK3) != iProver_top
% 8.02/1.48      | k7_relat_1(sK5,X0) = k1_xboole_0 ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_6021,c_54,c_2262]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7488,plain,
% 8.02/1.48      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 8.02/1.48      | r1_xboole_0(X0,sK3) != iProver_top ),
% 8.02/1.48      inference(renaming,[status(thm)],[c_7487]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_7495,plain,
% 8.02/1.48      ( k7_relat_1(sK5,sK0(sK3)) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_1761,c_7488]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2,plain,
% 8.02/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 8.02/1.48      inference(cnf_transformation,[],[f70]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_772,plain,
% 8.02/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 8.02/1.48      theory(equality) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2269,plain,
% 8.02/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_772]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2271,plain,
% 8.02/1.48      ( v1_xboole_0(sK3)
% 8.02/1.48      | ~ v1_xboole_0(k1_xboole_0)
% 8.02/1.48      | sK3 != k1_xboole_0 ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2269]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_8503,plain,
% 8.02/1.48      ( k7_relat_1(sK5,sK0(sK3)) = k1_xboole_0 ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_7495,c_42,c_2,c_2271]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_8506,plain,
% 8.02/1.48      ( r1_tarski(k1_relat_1(k1_xboole_0),sK0(sK3)) = iProver_top
% 8.02/1.48      | v1_relat_1(sK5) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_8503,c_1766]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_8521,plain,
% 8.02/1.48      ( r1_tarski(k1_xboole_0,sK0(sK3)) = iProver_top
% 8.02/1.48      | v1_relat_1(sK5) != iProver_top ),
% 8.02/1.48      inference(light_normalisation,[status(thm)],[c_8506,c_11]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_8906,plain,
% 8.02/1.48      ( r1_tarski(k1_xboole_0,sK0(sK3)) = iProver_top ),
% 8.02/1.48      inference(global_propositional_subsumption,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_8521,c_54,c_2262]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_8911,plain,
% 8.02/1.48      ( k9_relat_1(k7_relat_1(X0,sK0(sK3)),k1_xboole_0) = k9_relat_1(X0,k1_xboole_0)
% 8.02/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_8906,c_1770]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_10898,plain,
% 8.02/1.48      ( k9_relat_1(k7_relat_1(sK5,sK0(sK3)),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3005,c_8911]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_10900,plain,
% 8.02/1.48      ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 8.02/1.48      inference(light_normalisation,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_10898,c_7417,c_8503]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3159,plain,
% 8.02/1.48      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3005,c_1771]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3655,plain,
% 8.02/1.48      ( k9_relat_1(sK5,X0) != k1_xboole_0
% 8.02/1.48      | k7_relat_1(sK5,X0) = k1_xboole_0
% 8.02/1.48      | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
% 8.02/1.48      inference(superposition,[status(thm)],[c_3159,c_1768]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_3672,plain,
% 8.02/1.48      ( k9_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 8.02/1.48      | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0
% 8.02/1.48      | v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) != iProver_top ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_3655]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2502,plain,
% 8.02/1.48      ( v1_relat_1(k7_relat_1(sK5,X0)) | ~ v1_relat_1(sK5) ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2506,plain,
% 8.02/1.48      ( v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top
% 8.02/1.48      | v1_relat_1(sK5) != iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_2508,plain,
% 8.02/1.48      ( v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) = iProver_top
% 8.02/1.48      | v1_relat_1(sK5) != iProver_top ),
% 8.02/1.48      inference(instantiation,[status(thm)],[c_2506]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(c_48,plain,
% 8.02/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 8.02/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 8.02/1.48  
% 8.02/1.48  cnf(contradiction,plain,
% 8.02/1.48      ( $false ),
% 8.02/1.48      inference(minisat,
% 8.02/1.48                [status(thm)],
% 8.02/1.48                [c_30989,c_28626,c_19733,c_10900,c_3672,c_2508,c_2262,
% 8.02/1.48                 c_54,c_53,c_52,c_50,c_48,c_47]) ).
% 8.02/1.48  
% 8.02/1.48  
% 8.02/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 8.02/1.48  
% 8.02/1.48  ------                               Statistics
% 8.02/1.48  
% 8.02/1.48  ------ Selected
% 8.02/1.48  
% 8.02/1.48  total_time:                             0.903
% 8.02/1.48  
%------------------------------------------------------------------------------
