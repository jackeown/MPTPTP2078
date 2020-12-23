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
% DateTime   : Thu Dec  3 12:21:32 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  251 (1629 expanded)
%              Number of clauses        :  145 ( 408 expanded)
%              Number of leaves         :   26 ( 575 expanded)
%              Depth                    :   24
%              Number of atoms          : 1261 (17869 expanded)
%              Number of equality atoms :  442 (4139 expanded)
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

fof(f44,plain,(
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
    inference(flattening,[],[f44])).

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f45,f61,f60,f59,f58,f57,f56])).

fof(f100,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f104,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f102,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f107,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f62])).

fof(f105,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f108,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f62])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f95,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f62])).

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

fof(f40,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(nnf_transformation,[],[f41])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

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
    inference(cnf_transformation,[],[f55])).

fof(f119,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f42])).

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
    inference(cnf_transformation,[],[f43])).

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
    inference(cnf_transformation,[],[f43])).

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
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f106,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f103,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

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
    inference(cnf_transformation,[],[f55])).

fof(f118,plain,(
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

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f114,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f2,axiom,(
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
    inference(rectify,[],[f2])).

fof(f23,plain,(
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

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f47])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2500,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3720,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_2514])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_338,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_339,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_338])).

cnf(c_427,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_339])).

cnf(c_2492,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_6262,plain,
    ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_3720,c_2492])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2503,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2511,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4823,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_2511])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_52,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4993,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4823,c_52])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2506,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4822,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_2511])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_55,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4895,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4822,c_55])).

cnf(c_31,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_4898,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_4895,c_31])).

cnf(c_4996,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_4993,c_4898])).

cnf(c_6401,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_6262,c_4996])).

cnf(c_17,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_38,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_641,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_642,plain,
    ( r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_644,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_42,c_40])).

cnf(c_2490,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2524,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4034,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2490,c_2524])).

cnf(c_6402,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6401,c_4034])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f98])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f119])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f92])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_244,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_30,c_29,c_28])).

cnf(c_245,plain,
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
    inference(renaming,[status(thm)],[c_244])).

cnf(c_2494,plain,
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
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_4899,plain,
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
    inference(superposition,[status(thm)],[c_4895,c_2494])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_46,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_49,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_56,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_57,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5151,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4899,c_46,c_49,c_55,c_56,c_57])).

cnf(c_5152,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5151])).

cnf(c_5158,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_5152])).

cnf(c_47,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_53,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6000,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5158,c_47,c_52,c_53,c_54])).

cnf(c_6001,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6000])).

cnf(c_6414,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6262,c_6001])).

cnf(c_6415,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6414,c_4034])).

cnf(c_6416,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6415,c_6262])).

cnf(c_6417,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6416,c_4034])).

cnf(c_6431,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6417])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_251,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_30,c_29,c_28])).

cnf(c_252,plain,
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
    inference(renaming,[status(thm)],[c_251])).

cnf(c_2493,plain,
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
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_4900,plain,
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
    inference(superposition,[status(thm)],[c_4895,c_2493])).

cnf(c_6034,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4900,c_46,c_49,c_55,c_56,c_57])).

cnf(c_6035,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6034])).

cnf(c_6041,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_6035])).

cnf(c_6046,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6041,c_47,c_52,c_53,c_54])).

cnf(c_6047,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6046])).

cnf(c_6413,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6262,c_6047])).

cnf(c_6418,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6413,c_4034])).

cnf(c_6419,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6418,c_6262])).

cnf(c_6420,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6419,c_4034])).

cnf(c_6432,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6420])).

cnf(c_7807,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6402,c_44,c_41,c_39,c_6431,c_6432])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2517,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2516,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4555,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_2516])).

cnf(c_813,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k1_xboole_0 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_9])).

cnf(c_814,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_820,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_814,c_6])).

cnf(c_822,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_5896,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4555,c_822])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2519,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2521,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_430,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_339])).

cnf(c_2491,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_3794,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_2491])).

cnf(c_6363,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2519,c_3794])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_23,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_578,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_19,c_23])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_23,c_19,c_18])).

cnf(c_583,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_654,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_20,c_583])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_23,c_20,c_19,c_18])).

cnf(c_659,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_658])).

cnf(c_2489,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_3424,plain,
    ( k1_relat_1(sK6) = sK4
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_2489])).

cnf(c_2692,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK2)
    | k1_relat_1(X0) = X1 ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_2890,plain,
    ( ~ v1_funct_2(sK6,X0,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | k1_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_2692])).

cnf(c_3275,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | k1_relat_1(sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_2890])).

cnf(c_3614,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_43,c_34,c_33,c_32,c_3275])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2513,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4560,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_2513])).

cnf(c_2512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4505,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_2512])).

cnf(c_4724,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4560,c_4505])).

cnf(c_4725,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4724])).

cnf(c_6394,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6363,c_4725])).

cnf(c_7403,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5896,c_6394])).

cnf(c_3421,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_2489])).

cnf(c_2895,plain,
    ( ~ v1_funct_2(sK5,X0,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | k1_relat_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_2692])).

cnf(c_2897,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2895])).

cnf(c_3527,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3421,c_43,c_37,c_36,c_35,c_2897])).

cnf(c_4561,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3527,c_2513])).

cnf(c_4506,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_2512])).

cnf(c_5144,plain,
    ( r1_xboole_0(X0,sK3) != iProver_top
    | k7_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4561,c_4506])).

cnf(c_5145,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5144])).

cnf(c_6395,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6363,c_5145])).

cnf(c_7405,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5896,c_6395])).

cnf(c_7809,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7807,c_7403,c_7405])).

cnf(c_7810,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7809])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.06/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.06/0.99  
% 4.06/0.99  ------  iProver source info
% 4.06/0.99  
% 4.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.06/0.99  git: non_committed_changes: false
% 4.06/0.99  git: last_make_outside_of_git: false
% 4.06/0.99  
% 4.06/0.99  ------ 
% 4.06/0.99  
% 4.06/0.99  ------ Input Options
% 4.06/0.99  
% 4.06/0.99  --out_options                           all
% 4.06/0.99  --tptp_safe_out                         true
% 4.06/0.99  --problem_path                          ""
% 4.06/0.99  --include_path                          ""
% 4.06/0.99  --clausifier                            res/vclausify_rel
% 4.06/0.99  --clausifier_options                    ""
% 4.06/0.99  --stdin                                 false
% 4.06/0.99  --stats_out                             all
% 4.06/0.99  
% 4.06/0.99  ------ General Options
% 4.06/0.99  
% 4.06/0.99  --fof                                   false
% 4.06/0.99  --time_out_real                         305.
% 4.06/0.99  --time_out_virtual                      -1.
% 4.06/0.99  --symbol_type_check                     false
% 4.06/0.99  --clausify_out                          false
% 4.06/0.99  --sig_cnt_out                           false
% 4.06/0.99  --trig_cnt_out                          false
% 4.06/0.99  --trig_cnt_out_tolerance                1.
% 4.06/0.99  --trig_cnt_out_sk_spl                   false
% 4.06/0.99  --abstr_cl_out                          false
% 4.06/0.99  
% 4.06/0.99  ------ Global Options
% 4.06/0.99  
% 4.06/0.99  --schedule                              default
% 4.06/0.99  --add_important_lit                     false
% 4.06/0.99  --prop_solver_per_cl                    1000
% 4.06/0.99  --min_unsat_core                        false
% 4.06/0.99  --soft_assumptions                      false
% 4.06/0.99  --soft_lemma_size                       3
% 4.06/0.99  --prop_impl_unit_size                   0
% 4.06/0.99  --prop_impl_unit                        []
% 4.06/0.99  --share_sel_clauses                     true
% 4.06/0.99  --reset_solvers                         false
% 4.06/0.99  --bc_imp_inh                            [conj_cone]
% 4.06/0.99  --conj_cone_tolerance                   3.
% 4.06/0.99  --extra_neg_conj                        none
% 4.06/0.99  --large_theory_mode                     true
% 4.06/0.99  --prolific_symb_bound                   200
% 4.06/0.99  --lt_threshold                          2000
% 4.06/0.99  --clause_weak_htbl                      true
% 4.06/0.99  --gc_record_bc_elim                     false
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing Options
% 4.06/0.99  
% 4.06/0.99  --preprocessing_flag                    true
% 4.06/0.99  --time_out_prep_mult                    0.1
% 4.06/0.99  --splitting_mode                        input
% 4.06/0.99  --splitting_grd                         true
% 4.06/0.99  --splitting_cvd                         false
% 4.06/0.99  --splitting_cvd_svl                     false
% 4.06/0.99  --splitting_nvd                         32
% 4.06/0.99  --sub_typing                            true
% 4.06/0.99  --prep_gs_sim                           true
% 4.06/0.99  --prep_unflatten                        true
% 4.06/0.99  --prep_res_sim                          true
% 4.06/0.99  --prep_upred                            true
% 4.06/0.99  --prep_sem_filter                       exhaustive
% 4.06/0.99  --prep_sem_filter_out                   false
% 4.06/0.99  --pred_elim                             true
% 4.06/0.99  --res_sim_input                         true
% 4.06/0.99  --eq_ax_congr_red                       true
% 4.06/0.99  --pure_diseq_elim                       true
% 4.06/0.99  --brand_transform                       false
% 4.06/0.99  --non_eq_to_eq                          false
% 4.06/0.99  --prep_def_merge                        true
% 4.06/0.99  --prep_def_merge_prop_impl              false
% 4.06/0.99  --prep_def_merge_mbd                    true
% 4.06/0.99  --prep_def_merge_tr_red                 false
% 4.06/0.99  --prep_def_merge_tr_cl                  false
% 4.06/0.99  --smt_preprocessing                     true
% 4.06/0.99  --smt_ac_axioms                         fast
% 4.06/0.99  --preprocessed_out                      false
% 4.06/0.99  --preprocessed_stats                    false
% 4.06/0.99  
% 4.06/0.99  ------ Abstraction refinement Options
% 4.06/0.99  
% 4.06/0.99  --abstr_ref                             []
% 4.06/0.99  --abstr_ref_prep                        false
% 4.06/0.99  --abstr_ref_until_sat                   false
% 4.06/0.99  --abstr_ref_sig_restrict                funpre
% 4.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.06/0.99  --abstr_ref_under                       []
% 4.06/0.99  
% 4.06/0.99  ------ SAT Options
% 4.06/0.99  
% 4.06/0.99  --sat_mode                              false
% 4.06/0.99  --sat_fm_restart_options                ""
% 4.06/0.99  --sat_gr_def                            false
% 4.06/0.99  --sat_epr_types                         true
% 4.06/0.99  --sat_non_cyclic_types                  false
% 4.06/0.99  --sat_finite_models                     false
% 4.06/0.99  --sat_fm_lemmas                         false
% 4.06/0.99  --sat_fm_prep                           false
% 4.06/0.99  --sat_fm_uc_incr                        true
% 4.06/0.99  --sat_out_model                         small
% 4.06/0.99  --sat_out_clauses                       false
% 4.06/0.99  
% 4.06/0.99  ------ QBF Options
% 4.06/0.99  
% 4.06/0.99  --qbf_mode                              false
% 4.06/0.99  --qbf_elim_univ                         false
% 4.06/0.99  --qbf_dom_inst                          none
% 4.06/0.99  --qbf_dom_pre_inst                      false
% 4.06/0.99  --qbf_sk_in                             false
% 4.06/0.99  --qbf_pred_elim                         true
% 4.06/0.99  --qbf_split                             512
% 4.06/0.99  
% 4.06/0.99  ------ BMC1 Options
% 4.06/0.99  
% 4.06/0.99  --bmc1_incremental                      false
% 4.06/0.99  --bmc1_axioms                           reachable_all
% 4.06/0.99  --bmc1_min_bound                        0
% 4.06/0.99  --bmc1_max_bound                        -1
% 4.06/0.99  --bmc1_max_bound_default                -1
% 4.06/0.99  --bmc1_symbol_reachability              true
% 4.06/0.99  --bmc1_property_lemmas                  false
% 4.06/0.99  --bmc1_k_induction                      false
% 4.06/0.99  --bmc1_non_equiv_states                 false
% 4.06/0.99  --bmc1_deadlock                         false
% 4.06/0.99  --bmc1_ucm                              false
% 4.06/0.99  --bmc1_add_unsat_core                   none
% 4.06/0.99  --bmc1_unsat_core_children              false
% 4.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.06/0.99  --bmc1_out_stat                         full
% 4.06/0.99  --bmc1_ground_init                      false
% 4.06/0.99  --bmc1_pre_inst_next_state              false
% 4.06/0.99  --bmc1_pre_inst_state                   false
% 4.06/0.99  --bmc1_pre_inst_reach_state             false
% 4.06/0.99  --bmc1_out_unsat_core                   false
% 4.06/0.99  --bmc1_aig_witness_out                  false
% 4.06/0.99  --bmc1_verbose                          false
% 4.06/0.99  --bmc1_dump_clauses_tptp                false
% 4.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.06/0.99  --bmc1_dump_file                        -
% 4.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.06/0.99  --bmc1_ucm_extend_mode                  1
% 4.06/0.99  --bmc1_ucm_init_mode                    2
% 4.06/0.99  --bmc1_ucm_cone_mode                    none
% 4.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.06/0.99  --bmc1_ucm_relax_model                  4
% 4.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.06/0.99  --bmc1_ucm_layered_model                none
% 4.06/0.99  --bmc1_ucm_max_lemma_size               10
% 4.06/0.99  
% 4.06/0.99  ------ AIG Options
% 4.06/0.99  
% 4.06/0.99  --aig_mode                              false
% 4.06/0.99  
% 4.06/0.99  ------ Instantiation Options
% 4.06/0.99  
% 4.06/0.99  --instantiation_flag                    true
% 4.06/0.99  --inst_sos_flag                         true
% 4.06/0.99  --inst_sos_phase                        true
% 4.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.06/0.99  --inst_lit_sel_side                     num_symb
% 4.06/0.99  --inst_solver_per_active                1400
% 4.06/0.99  --inst_solver_calls_frac                1.
% 4.06/0.99  --inst_passive_queue_type               priority_queues
% 4.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.06/0.99  --inst_passive_queues_freq              [25;2]
% 4.06/0.99  --inst_dismatching                      true
% 4.06/0.99  --inst_eager_unprocessed_to_passive     true
% 4.06/0.99  --inst_prop_sim_given                   true
% 4.06/0.99  --inst_prop_sim_new                     false
% 4.06/0.99  --inst_subs_new                         false
% 4.06/0.99  --inst_eq_res_simp                      false
% 4.06/0.99  --inst_subs_given                       false
% 4.06/0.99  --inst_orphan_elimination               true
% 4.06/0.99  --inst_learning_loop_flag               true
% 4.06/0.99  --inst_learning_start                   3000
% 4.06/0.99  --inst_learning_factor                  2
% 4.06/0.99  --inst_start_prop_sim_after_learn       3
% 4.06/0.99  --inst_sel_renew                        solver
% 4.06/0.99  --inst_lit_activity_flag                true
% 4.06/0.99  --inst_restr_to_given                   false
% 4.06/0.99  --inst_activity_threshold               500
% 4.06/0.99  --inst_out_proof                        true
% 4.06/0.99  
% 4.06/0.99  ------ Resolution Options
% 4.06/0.99  
% 4.06/0.99  --resolution_flag                       true
% 4.06/0.99  --res_lit_sel                           adaptive
% 4.06/0.99  --res_lit_sel_side                      none
% 4.06/0.99  --res_ordering                          kbo
% 4.06/0.99  --res_to_prop_solver                    active
% 4.06/0.99  --res_prop_simpl_new                    false
% 4.06/0.99  --res_prop_simpl_given                  true
% 4.06/0.99  --res_passive_queue_type                priority_queues
% 4.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.06/0.99  --res_passive_queues_freq               [15;5]
% 4.06/0.99  --res_forward_subs                      full
% 4.06/0.99  --res_backward_subs                     full
% 4.06/0.99  --res_forward_subs_resolution           true
% 4.06/0.99  --res_backward_subs_resolution          true
% 4.06/0.99  --res_orphan_elimination                true
% 4.06/0.99  --res_time_limit                        2.
% 4.06/0.99  --res_out_proof                         true
% 4.06/0.99  
% 4.06/0.99  ------ Superposition Options
% 4.06/0.99  
% 4.06/0.99  --superposition_flag                    true
% 4.06/0.99  --sup_passive_queue_type                priority_queues
% 4.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.06/0.99  --demod_completeness_check              fast
% 4.06/0.99  --demod_use_ground                      true
% 4.06/0.99  --sup_to_prop_solver                    passive
% 4.06/0.99  --sup_prop_simpl_new                    true
% 4.06/0.99  --sup_prop_simpl_given                  true
% 4.06/0.99  --sup_fun_splitting                     true
% 4.06/0.99  --sup_smt_interval                      50000
% 4.06/0.99  
% 4.06/0.99  ------ Superposition Simplification Setup
% 4.06/0.99  
% 4.06/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.06/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.06/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.06/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.06/0.99  --sup_immed_triv                        [TrivRules]
% 4.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.99  --sup_immed_bw_main                     []
% 4.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.99  --sup_input_bw                          []
% 4.06/0.99  
% 4.06/0.99  ------ Combination Options
% 4.06/0.99  
% 4.06/0.99  --comb_res_mult                         3
% 4.06/0.99  --comb_sup_mult                         2
% 4.06/0.99  --comb_inst_mult                        10
% 4.06/0.99  
% 4.06/0.99  ------ Debug Options
% 4.06/0.99  
% 4.06/0.99  --dbg_backtrace                         false
% 4.06/0.99  --dbg_dump_prop_clauses                 false
% 4.06/0.99  --dbg_dump_prop_clauses_file            -
% 4.06/0.99  --dbg_out_stat                          false
% 4.06/0.99  ------ Parsing...
% 4.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.06/0.99  ------ Proving...
% 4.06/0.99  ------ Problem Properties 
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  clauses                                 38
% 4.06/0.99  conjectures                             13
% 4.06/0.99  EPR                                     16
% 4.06/0.99  Horn                                    29
% 4.06/0.99  unary                                   15
% 4.06/0.99  binary                                  9
% 4.06/0.99  lits                                    143
% 4.06/0.99  lits eq                                 17
% 4.06/0.99  fd_pure                                 0
% 4.06/0.99  fd_pseudo                               0
% 4.06/0.99  fd_cond                                 1
% 4.06/0.99  fd_pseudo_cond                          2
% 4.06/0.99  AC symbols                              0
% 4.06/0.99  
% 4.06/0.99  ------ Schedule dynamic 5 is on 
% 4.06/0.99  
% 4.06/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  ------ 
% 4.06/0.99  Current options:
% 4.06/0.99  ------ 
% 4.06/0.99  
% 4.06/0.99  ------ Input Options
% 4.06/0.99  
% 4.06/0.99  --out_options                           all
% 4.06/0.99  --tptp_safe_out                         true
% 4.06/0.99  --problem_path                          ""
% 4.06/0.99  --include_path                          ""
% 4.06/0.99  --clausifier                            res/vclausify_rel
% 4.06/0.99  --clausifier_options                    ""
% 4.06/0.99  --stdin                                 false
% 4.06/0.99  --stats_out                             all
% 4.06/0.99  
% 4.06/0.99  ------ General Options
% 4.06/0.99  
% 4.06/0.99  --fof                                   false
% 4.06/0.99  --time_out_real                         305.
% 4.06/0.99  --time_out_virtual                      -1.
% 4.06/0.99  --symbol_type_check                     false
% 4.06/0.99  --clausify_out                          false
% 4.06/0.99  --sig_cnt_out                           false
% 4.06/0.99  --trig_cnt_out                          false
% 4.06/0.99  --trig_cnt_out_tolerance                1.
% 4.06/0.99  --trig_cnt_out_sk_spl                   false
% 4.06/0.99  --abstr_cl_out                          false
% 4.06/0.99  
% 4.06/0.99  ------ Global Options
% 4.06/0.99  
% 4.06/0.99  --schedule                              default
% 4.06/0.99  --add_important_lit                     false
% 4.06/0.99  --prop_solver_per_cl                    1000
% 4.06/0.99  --min_unsat_core                        false
% 4.06/0.99  --soft_assumptions                      false
% 4.06/0.99  --soft_lemma_size                       3
% 4.06/0.99  --prop_impl_unit_size                   0
% 4.06/0.99  --prop_impl_unit                        []
% 4.06/0.99  --share_sel_clauses                     true
% 4.06/0.99  --reset_solvers                         false
% 4.06/0.99  --bc_imp_inh                            [conj_cone]
% 4.06/0.99  --conj_cone_tolerance                   3.
% 4.06/0.99  --extra_neg_conj                        none
% 4.06/0.99  --large_theory_mode                     true
% 4.06/0.99  --prolific_symb_bound                   200
% 4.06/0.99  --lt_threshold                          2000
% 4.06/0.99  --clause_weak_htbl                      true
% 4.06/0.99  --gc_record_bc_elim                     false
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing Options
% 4.06/0.99  
% 4.06/0.99  --preprocessing_flag                    true
% 4.06/0.99  --time_out_prep_mult                    0.1
% 4.06/0.99  --splitting_mode                        input
% 4.06/0.99  --splitting_grd                         true
% 4.06/0.99  --splitting_cvd                         false
% 4.06/0.99  --splitting_cvd_svl                     false
% 4.06/0.99  --splitting_nvd                         32
% 4.06/0.99  --sub_typing                            true
% 4.06/0.99  --prep_gs_sim                           true
% 4.06/0.99  --prep_unflatten                        true
% 4.06/0.99  --prep_res_sim                          true
% 4.06/0.99  --prep_upred                            true
% 4.06/0.99  --prep_sem_filter                       exhaustive
% 4.06/0.99  --prep_sem_filter_out                   false
% 4.06/0.99  --pred_elim                             true
% 4.06/0.99  --res_sim_input                         true
% 4.06/0.99  --eq_ax_congr_red                       true
% 4.06/0.99  --pure_diseq_elim                       true
% 4.06/0.99  --brand_transform                       false
% 4.06/0.99  --non_eq_to_eq                          false
% 4.06/0.99  --prep_def_merge                        true
% 4.06/0.99  --prep_def_merge_prop_impl              false
% 4.06/0.99  --prep_def_merge_mbd                    true
% 4.06/0.99  --prep_def_merge_tr_red                 false
% 4.06/0.99  --prep_def_merge_tr_cl                  false
% 4.06/0.99  --smt_preprocessing                     true
% 4.06/0.99  --smt_ac_axioms                         fast
% 4.06/0.99  --preprocessed_out                      false
% 4.06/0.99  --preprocessed_stats                    false
% 4.06/0.99  
% 4.06/0.99  ------ Abstraction refinement Options
% 4.06/0.99  
% 4.06/0.99  --abstr_ref                             []
% 4.06/0.99  --abstr_ref_prep                        false
% 4.06/0.99  --abstr_ref_until_sat                   false
% 4.06/0.99  --abstr_ref_sig_restrict                funpre
% 4.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.06/0.99  --abstr_ref_under                       []
% 4.06/0.99  
% 4.06/0.99  ------ SAT Options
% 4.06/0.99  
% 4.06/0.99  --sat_mode                              false
% 4.06/0.99  --sat_fm_restart_options                ""
% 4.06/0.99  --sat_gr_def                            false
% 4.06/0.99  --sat_epr_types                         true
% 4.06/0.99  --sat_non_cyclic_types                  false
% 4.06/0.99  --sat_finite_models                     false
% 4.06/0.99  --sat_fm_lemmas                         false
% 4.06/0.99  --sat_fm_prep                           false
% 4.06/0.99  --sat_fm_uc_incr                        true
% 4.06/0.99  --sat_out_model                         small
% 4.06/0.99  --sat_out_clauses                       false
% 4.06/0.99  
% 4.06/0.99  ------ QBF Options
% 4.06/0.99  
% 4.06/0.99  --qbf_mode                              false
% 4.06/0.99  --qbf_elim_univ                         false
% 4.06/0.99  --qbf_dom_inst                          none
% 4.06/0.99  --qbf_dom_pre_inst                      false
% 4.06/0.99  --qbf_sk_in                             false
% 4.06/0.99  --qbf_pred_elim                         true
% 4.06/0.99  --qbf_split                             512
% 4.06/0.99  
% 4.06/0.99  ------ BMC1 Options
% 4.06/0.99  
% 4.06/0.99  --bmc1_incremental                      false
% 4.06/0.99  --bmc1_axioms                           reachable_all
% 4.06/0.99  --bmc1_min_bound                        0
% 4.06/0.99  --bmc1_max_bound                        -1
% 4.06/0.99  --bmc1_max_bound_default                -1
% 4.06/0.99  --bmc1_symbol_reachability              true
% 4.06/0.99  --bmc1_property_lemmas                  false
% 4.06/0.99  --bmc1_k_induction                      false
% 4.06/0.99  --bmc1_non_equiv_states                 false
% 4.06/0.99  --bmc1_deadlock                         false
% 4.06/0.99  --bmc1_ucm                              false
% 4.06/0.99  --bmc1_add_unsat_core                   none
% 4.06/0.99  --bmc1_unsat_core_children              false
% 4.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.06/0.99  --bmc1_out_stat                         full
% 4.06/0.99  --bmc1_ground_init                      false
% 4.06/0.99  --bmc1_pre_inst_next_state              false
% 4.06/0.99  --bmc1_pre_inst_state                   false
% 4.06/0.99  --bmc1_pre_inst_reach_state             false
% 4.06/0.99  --bmc1_out_unsat_core                   false
% 4.06/0.99  --bmc1_aig_witness_out                  false
% 4.06/0.99  --bmc1_verbose                          false
% 4.06/0.99  --bmc1_dump_clauses_tptp                false
% 4.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.06/0.99  --bmc1_dump_file                        -
% 4.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.06/0.99  --bmc1_ucm_extend_mode                  1
% 4.06/0.99  --bmc1_ucm_init_mode                    2
% 4.06/0.99  --bmc1_ucm_cone_mode                    none
% 4.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.06/0.99  --bmc1_ucm_relax_model                  4
% 4.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.06/0.99  --bmc1_ucm_layered_model                none
% 4.06/0.99  --bmc1_ucm_max_lemma_size               10
% 4.06/0.99  
% 4.06/0.99  ------ AIG Options
% 4.06/0.99  
% 4.06/0.99  --aig_mode                              false
% 4.06/0.99  
% 4.06/0.99  ------ Instantiation Options
% 4.06/0.99  
% 4.06/0.99  --instantiation_flag                    true
% 4.06/0.99  --inst_sos_flag                         true
% 4.06/0.99  --inst_sos_phase                        true
% 4.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.06/0.99  --inst_lit_sel_side                     none
% 4.06/0.99  --inst_solver_per_active                1400
% 4.06/0.99  --inst_solver_calls_frac                1.
% 4.06/0.99  --inst_passive_queue_type               priority_queues
% 4.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.06/0.99  --inst_passive_queues_freq              [25;2]
% 4.06/0.99  --inst_dismatching                      true
% 4.06/0.99  --inst_eager_unprocessed_to_passive     true
% 4.06/0.99  --inst_prop_sim_given                   true
% 4.06/0.99  --inst_prop_sim_new                     false
% 4.06/0.99  --inst_subs_new                         false
% 4.06/0.99  --inst_eq_res_simp                      false
% 4.06/0.99  --inst_subs_given                       false
% 4.06/0.99  --inst_orphan_elimination               true
% 4.06/0.99  --inst_learning_loop_flag               true
% 4.06/0.99  --inst_learning_start                   3000
% 4.06/0.99  --inst_learning_factor                  2
% 4.06/0.99  --inst_start_prop_sim_after_learn       3
% 4.06/0.99  --inst_sel_renew                        solver
% 4.06/0.99  --inst_lit_activity_flag                true
% 4.06/0.99  --inst_restr_to_given                   false
% 4.06/0.99  --inst_activity_threshold               500
% 4.06/0.99  --inst_out_proof                        true
% 4.06/0.99  
% 4.06/0.99  ------ Resolution Options
% 4.06/0.99  
% 4.06/0.99  --resolution_flag                       false
% 4.06/0.99  --res_lit_sel                           adaptive
% 4.06/0.99  --res_lit_sel_side                      none
% 4.06/0.99  --res_ordering                          kbo
% 4.06/0.99  --res_to_prop_solver                    active
% 4.06/0.99  --res_prop_simpl_new                    false
% 4.06/0.99  --res_prop_simpl_given                  true
% 4.06/0.99  --res_passive_queue_type                priority_queues
% 4.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.06/0.99  --res_passive_queues_freq               [15;5]
% 4.06/0.99  --res_forward_subs                      full
% 4.06/0.99  --res_backward_subs                     full
% 4.06/0.99  --res_forward_subs_resolution           true
% 4.06/0.99  --res_backward_subs_resolution          true
% 4.06/0.99  --res_orphan_elimination                true
% 4.06/0.99  --res_time_limit                        2.
% 4.06/0.99  --res_out_proof                         true
% 4.06/0.99  
% 4.06/0.99  ------ Superposition Options
% 4.06/0.99  
% 4.06/0.99  --superposition_flag                    true
% 4.06/0.99  --sup_passive_queue_type                priority_queues
% 4.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.06/0.99  --demod_completeness_check              fast
% 4.06/0.99  --demod_use_ground                      true
% 4.06/0.99  --sup_to_prop_solver                    passive
% 4.06/0.99  --sup_prop_simpl_new                    true
% 4.06/0.99  --sup_prop_simpl_given                  true
% 4.06/0.99  --sup_fun_splitting                     true
% 4.06/0.99  --sup_smt_interval                      50000
% 4.06/0.99  
% 4.06/0.99  ------ Superposition Simplification Setup
% 4.06/0.99  
% 4.06/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.06/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.06/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.06/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.06/0.99  --sup_immed_triv                        [TrivRules]
% 4.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.99  --sup_immed_bw_main                     []
% 4.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.99  --sup_input_bw                          []
% 4.06/0.99  
% 4.06/0.99  ------ Combination Options
% 4.06/0.99  
% 4.06/0.99  --comb_res_mult                         3
% 4.06/0.99  --comb_sup_mult                         2
% 4.06/0.99  --comb_inst_mult                        10
% 4.06/0.99  
% 4.06/0.99  ------ Debug Options
% 4.06/0.99  
% 4.06/0.99  --dbg_backtrace                         false
% 4.06/0.99  --dbg_dump_prop_clauses                 false
% 4.06/0.99  --dbg_dump_prop_clauses_file            -
% 4.06/0.99  --dbg_out_stat                          false
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  ------ Proving...
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  % SZS status Theorem for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99   Resolution empty clause
% 4.06/0.99  
% 4.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  fof(f19,conjecture,(
% 4.06/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f20,negated_conjecture,(
% 4.06/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 4.06/0.99    inference(negated_conjecture,[],[f19])).
% 4.06/0.99  
% 4.06/0.99  fof(f44,plain,(
% 4.06/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.06/0.99    inference(ennf_transformation,[],[f20])).
% 4.06/0.99  
% 4.06/0.99  fof(f45,plain,(
% 4.06/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.06/0.99    inference(flattening,[],[f44])).
% 4.06/0.99  
% 4.06/0.99  fof(f61,plain,(
% 4.06/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f60,plain,(
% 4.06/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f59,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f58,plain,(
% 4.06/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f57,plain,(
% 4.06/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f56,plain,(
% 4.06/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f62,plain,(
% 4.06/0.99    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 4.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f45,f61,f60,f59,f58,f57,f56])).
% 4.06/0.99  
% 4.06/0.99  fof(f100,plain,(
% 4.06/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f8,axiom,(
% 4.06/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f51,plain,(
% 4.06/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.06/0.99    inference(nnf_transformation,[],[f8])).
% 4.06/0.99  
% 4.06/0.99  fof(f76,plain,(
% 4.06/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f51])).
% 4.06/0.99  
% 4.06/0.99  fof(f6,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f27,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.06/0.99    inference(ennf_transformation,[],[f6])).
% 4.06/0.99  
% 4.06/0.99  fof(f74,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f27])).
% 4.06/0.99  
% 4.06/0.99  fof(f7,axiom,(
% 4.06/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f75,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f7])).
% 4.06/0.99  
% 4.06/0.99  fof(f111,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.06/0.99    inference(definition_unfolding,[],[f74,f75])).
% 4.06/0.99  
% 4.06/0.99  fof(f77,plain,(
% 4.06/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f51])).
% 4.06/0.99  
% 4.06/0.99  fof(f104,plain,(
% 4.06/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f16,axiom,(
% 4.06/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f38,plain,(
% 4.06/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.06/0.99    inference(ennf_transformation,[],[f16])).
% 4.06/0.99  
% 4.06/0.99  fof(f39,plain,(
% 4.06/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.06/0.99    inference(flattening,[],[f38])).
% 4.06/0.99  
% 4.06/0.99  fof(f88,plain,(
% 4.06/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f39])).
% 4.06/0.99  
% 4.06/0.99  fof(f102,plain,(
% 4.06/0.99    v1_funct_1(sK5)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f107,plain,(
% 4.06/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f105,plain,(
% 4.06/0.99    v1_funct_1(sK6)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f108,plain,(
% 4.06/0.99    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f11,axiom,(
% 4.06/0.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f30,plain,(
% 4.06/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 4.06/0.99    inference(ennf_transformation,[],[f11])).
% 4.06/0.99  
% 4.06/0.99  fof(f31,plain,(
% 4.06/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.06/0.99    inference(flattening,[],[f30])).
% 4.06/0.99  
% 4.06/0.99  fof(f52,plain,(
% 4.06/0.99    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.06/0.99    inference(nnf_transformation,[],[f31])).
% 4.06/0.99  
% 4.06/0.99  fof(f80,plain,(
% 4.06/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f52])).
% 4.06/0.99  
% 4.06/0.99  fof(f101,plain,(
% 4.06/0.99    r1_subset_1(sK3,sK4)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f97,plain,(
% 4.06/0.99    ~v1_xboole_0(sK3)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f99,plain,(
% 4.06/0.99    ~v1_xboole_0(sK4)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f1,axiom,(
% 4.06/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f46,plain,(
% 4.06/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.06/0.99    inference(nnf_transformation,[],[f1])).
% 4.06/0.99  
% 4.06/0.99  fof(f63,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f46])).
% 4.06/0.99  
% 4.06/0.99  fof(f110,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.06/0.99    inference(definition_unfolding,[],[f63,f75])).
% 4.06/0.99  
% 4.06/0.99  fof(f95,plain,(
% 4.06/0.99    ~v1_xboole_0(sK1)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f98,plain,(
% 4.06/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f17,axiom,(
% 4.06/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f40,plain,(
% 4.06/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.06/0.99    inference(ennf_transformation,[],[f17])).
% 4.06/0.99  
% 4.06/0.99  fof(f41,plain,(
% 4.06/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.06/0.99    inference(flattening,[],[f40])).
% 4.06/0.99  
% 4.06/0.99  fof(f54,plain,(
% 4.06/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.06/0.99    inference(nnf_transformation,[],[f41])).
% 4.06/0.99  
% 4.06/0.99  fof(f55,plain,(
% 4.06/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.06/0.99    inference(flattening,[],[f54])).
% 4.06/0.99  
% 4.06/0.99  fof(f89,plain,(
% 4.06/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f55])).
% 4.06/0.99  
% 4.06/0.99  fof(f119,plain,(
% 4.06/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.06/0.99    inference(equality_resolution,[],[f89])).
% 4.06/0.99  
% 4.06/0.99  fof(f18,axiom,(
% 4.06/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f42,plain,(
% 4.06/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 4.06/0.99    inference(ennf_transformation,[],[f18])).
% 4.06/0.99  
% 4.06/0.99  fof(f43,plain,(
% 4.06/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.06/0.99    inference(flattening,[],[f42])).
% 4.06/0.99  
% 4.06/0.99  fof(f92,plain,(
% 4.06/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f43])).
% 4.06/0.99  
% 4.06/0.99  fof(f93,plain,(
% 4.06/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f43])).
% 4.06/0.99  
% 4.06/0.99  fof(f94,plain,(
% 4.06/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f43])).
% 4.06/0.99  
% 4.06/0.99  fof(f96,plain,(
% 4.06/0.99    ~v1_xboole_0(sK2)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f106,plain,(
% 4.06/0.99    v1_funct_2(sK6,sK4,sK2)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f103,plain,(
% 4.06/0.99    v1_funct_2(sK5,sK3,sK2)),
% 4.06/0.99    inference(cnf_transformation,[],[f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f90,plain,(
% 4.06/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f55])).
% 4.06/0.99  
% 4.06/0.99  fof(f118,plain,(
% 4.06/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.06/0.99    inference(equality_resolution,[],[f90])).
% 4.06/0.99  
% 4.06/0.99  fof(f4,axiom,(
% 4.06/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f24,plain,(
% 4.06/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 4.06/0.99    inference(ennf_transformation,[],[f4])).
% 4.06/0.99  
% 4.06/0.99  fof(f71,plain,(
% 4.06/0.99    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f24])).
% 4.06/0.99  
% 4.06/0.99  fof(f114,plain,(
% 4.06/0.99    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 4.06/0.99    inference(equality_resolution,[],[f71])).
% 4.06/0.99  
% 4.06/0.99  fof(f5,axiom,(
% 4.06/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f25,plain,(
% 4.06/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 4.06/0.99    inference(ennf_transformation,[],[f5])).
% 4.06/0.99  
% 4.06/0.99  fof(f26,plain,(
% 4.06/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 4.06/0.99    inference(flattening,[],[f25])).
% 4.06/0.99  
% 4.06/0.99  fof(f73,plain,(
% 4.06/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f26])).
% 4.06/0.99  
% 4.06/0.99  fof(f3,axiom,(
% 4.06/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f49,plain,(
% 4.06/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.06/0.99    inference(nnf_transformation,[],[f3])).
% 4.06/0.99  
% 4.06/0.99  fof(f50,plain,(
% 4.06/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.06/0.99    inference(flattening,[],[f49])).
% 4.06/0.99  
% 4.06/0.99  fof(f69,plain,(
% 4.06/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.06/0.99    inference(cnf_transformation,[],[f50])).
% 4.06/0.99  
% 4.06/0.99  fof(f112,plain,(
% 4.06/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.06/0.99    inference(equality_resolution,[],[f69])).
% 4.06/0.99  
% 4.06/0.99  fof(f68,plain,(
% 4.06/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.06/0.99    inference(cnf_transformation,[],[f50])).
% 4.06/0.99  
% 4.06/0.99  fof(f113,plain,(
% 4.06/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.06/0.99    inference(equality_resolution,[],[f68])).
% 4.06/0.99  
% 4.06/0.99  fof(f2,axiom,(
% 4.06/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f21,plain,(
% 4.06/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.06/0.99    inference(rectify,[],[f2])).
% 4.06/0.99  
% 4.06/0.99  fof(f23,plain,(
% 4.06/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.06/0.99    inference(ennf_transformation,[],[f21])).
% 4.06/0.99  
% 4.06/0.99  fof(f47,plain,(
% 4.06/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f48,plain,(
% 4.06/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f47])).
% 4.06/0.99  
% 4.06/0.99  fof(f65,plain,(
% 4.06/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f48])).
% 4.06/0.99  
% 4.06/0.99  fof(f9,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f28,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.06/0.99    inference(ennf_transformation,[],[f9])).
% 4.06/0.99  
% 4.06/0.99  fof(f78,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f28])).
% 4.06/0.99  
% 4.06/0.99  fof(f14,axiom,(
% 4.06/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f34,plain,(
% 4.06/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 4.06/0.99    inference(ennf_transformation,[],[f14])).
% 4.06/0.99  
% 4.06/0.99  fof(f35,plain,(
% 4.06/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 4.06/0.99    inference(flattening,[],[f34])).
% 4.06/0.99  
% 4.06/0.99  fof(f85,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f35])).
% 4.06/0.99  
% 4.06/0.99  fof(f13,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f22,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 4.06/0.99    inference(pure_predicate_removal,[],[f13])).
% 4.06/0.99  
% 4.06/0.99  fof(f33,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(ennf_transformation,[],[f22])).
% 4.06/0.99  
% 4.06/0.99  fof(f83,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f33])).
% 4.06/0.99  
% 4.06/0.99  fof(f15,axiom,(
% 4.06/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f36,plain,(
% 4.06/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.06/0.99    inference(ennf_transformation,[],[f15])).
% 4.06/0.99  
% 4.06/0.99  fof(f37,plain,(
% 4.06/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.06/0.99    inference(flattening,[],[f36])).
% 4.06/0.99  
% 4.06/0.99  fof(f53,plain,(
% 4.06/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.06/0.99    inference(nnf_transformation,[],[f37])).
% 4.06/0.99  
% 4.06/0.99  fof(f86,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f53])).
% 4.06/0.99  
% 4.06/0.99  fof(f12,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f32,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(ennf_transformation,[],[f12])).
% 4.06/0.99  
% 4.06/0.99  fof(f82,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f32])).
% 4.06/0.99  
% 4.06/0.99  fof(f10,axiom,(
% 4.06/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 4.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f29,plain,(
% 4.06/0.99    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.06/0.99    inference(ennf_transformation,[],[f10])).
% 4.06/0.99  
% 4.06/0.99  fof(f79,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f29])).
% 4.06/0.99  
% 4.06/0.99  cnf(c_39,negated_conjecture,
% 4.06/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 4.06/0.99      inference(cnf_transformation,[],[f100]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2500,plain,
% 4.06/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_13,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2514,plain,
% 4.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.06/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3720,plain,
% 4.06/0.99      ( r1_tarski(sK4,sK1) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2500,c_2514]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_11,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.06/0.99      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 4.06/0.99      inference(cnf_transformation,[],[f111]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_12,plain,
% 4.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_338,plain,
% 4.06/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.06/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_339,plain,
% 4.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_338]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_427,plain,
% 4.06/0.99      ( ~ r1_tarski(X0,X1)
% 4.06/0.99      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 4.06/0.99      inference(bin_hyper_res,[status(thm)],[c_11,c_339]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2492,plain,
% 4.06/0.99      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 4.06/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6262,plain,
% 4.06/0.99      ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_3720,c_2492]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_35,negated_conjecture,
% 4.06/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 4.06/0.99      inference(cnf_transformation,[],[f104]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2503,plain,
% 4.06/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_24,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 4.06/0.99      inference(cnf_transformation,[],[f88]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2511,plain,
% 4.06/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 4.06/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.06/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4823,plain,
% 4.06/0.99      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 4.06/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2503,c_2511]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_37,negated_conjecture,
% 4.06/0.99      ( v1_funct_1(sK5) ),
% 4.06/0.99      inference(cnf_transformation,[],[f102]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_52,plain,
% 4.06/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4993,plain,
% 4.06/0.99      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 4.06/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4823,c_52]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_32,negated_conjecture,
% 4.06/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 4.06/0.99      inference(cnf_transformation,[],[f107]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2506,plain,
% 4.06/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4822,plain,
% 4.06/0.99      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 4.06/0.99      | v1_funct_1(sK6) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2506,c_2511]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_34,negated_conjecture,
% 4.06/0.99      ( v1_funct_1(sK6) ),
% 4.06/0.99      inference(cnf_transformation,[],[f105]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_55,plain,
% 4.06/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4895,plain,
% 4.06/0.99      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 4.06/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4822,c_55]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_31,negated_conjecture,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 4.06/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 4.06/0.99      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 4.06/0.99      inference(cnf_transformation,[],[f108]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4898,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 4.06/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 4.06/0.99      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_4895,c_31]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4996,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 4.06/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 4.06/0.99      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_4993,c_4898]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6401,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 4.06/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 4.06/0.99      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_6262,c_4996]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_17,plain,
% 4.06/0.99      ( ~ r1_subset_1(X0,X1)
% 4.06/0.99      | r1_xboole_0(X0,X1)
% 4.06/0.99      | v1_xboole_0(X1)
% 4.06/0.99      | v1_xboole_0(X0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f80]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_38,negated_conjecture,
% 4.06/0.99      ( r1_subset_1(sK3,sK4) ),
% 4.06/0.99      inference(cnf_transformation,[],[f101]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_641,plain,
% 4.06/0.99      ( r1_xboole_0(X0,X1)
% 4.06/0.99      | v1_xboole_0(X1)
% 4.06/0.99      | v1_xboole_0(X0)
% 4.06/0.99      | sK4 != X1
% 4.06/0.99      | sK3 != X0 ),
% 4.06/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_642,plain,
% 4.06/0.99      ( r1_xboole_0(sK3,sK4) | v1_xboole_0(sK4) | v1_xboole_0(sK3) ),
% 4.06/0.99      inference(unflattening,[status(thm)],[c_641]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_42,negated_conjecture,
% 4.06/0.99      ( ~ v1_xboole_0(sK3) ),
% 4.06/0.99      inference(cnf_transformation,[],[f97]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_40,negated_conjecture,
% 4.06/0.99      ( ~ v1_xboole_0(sK4) ),
% 4.06/0.99      inference(cnf_transformation,[],[f99]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_644,plain,
% 4.06/0.99      ( r1_xboole_0(sK3,sK4) ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_642,c_42,c_40]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2490,plain,
% 4.06/0.99      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1,plain,
% 4.06/0.99      ( ~ r1_xboole_0(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f110]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2524,plain,
% 4.06/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 4.06/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4034,plain,
% 4.06/0.99      ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2490,c_2524]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6402,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 4.06/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 4.06/0.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_6401,c_4034]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_44,negated_conjecture,
% 4.06/0.99      ( ~ v1_xboole_0(sK1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f95]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_41,negated_conjecture,
% 4.06/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 4.06/0.99      inference(cnf_transformation,[],[f98]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_27,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X3)
% 4.06/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X1)
% 4.06/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.06/0.99      inference(cnf_transformation,[],[f119]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_30,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X3)
% 4.06/0.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f92]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_29,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X3)
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f93]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_28,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X3)
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f94]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_244,plain,
% 4.06/0.99      ( ~ v1_funct_1(X3)
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X1)
% 4.06/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_27,c_30,c_29,c_28]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_245,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X3)
% 4.06/0.99      | v1_xboole_0(X1)
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_244]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2494,plain,
% 4.06/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 4.06/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.06/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.06/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.06/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.06/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.06/0.99      | v1_funct_1(X2) != iProver_top
% 4.06/0.99      | v1_funct_1(X5) != iProver_top
% 4.06/0.99      | v1_xboole_0(X1) = iProver_top
% 4.06/0.99      | v1_xboole_0(X3) = iProver_top
% 4.06/0.99      | v1_xboole_0(X4) = iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4899,plain,
% 4.06/0.99      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 4.06/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 4.06/0.99      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | v1_funct_1(X1) != iProver_top
% 4.06/0.99      | v1_funct_1(sK6) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top
% 4.06/0.99      | v1_xboole_0(X2) = iProver_top
% 4.06/0.99      | v1_xboole_0(sK2) = iProver_top
% 4.06/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4895,c_2494]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_43,negated_conjecture,
% 4.06/0.99      ( ~ v1_xboole_0(sK2) ),
% 4.06/0.99      inference(cnf_transformation,[],[f96]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_46,plain,
% 4.06/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_49,plain,
% 4.06/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_33,negated_conjecture,
% 4.06/0.99      ( v1_funct_2(sK6,sK4,sK2) ),
% 4.06/0.99      inference(cnf_transformation,[],[f106]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_56,plain,
% 4.06/0.99      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_57,plain,
% 4.06/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5151,plain,
% 4.06/0.99      ( v1_funct_1(X1) != iProver_top
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 4.06/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 4.06/0.99      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top
% 4.06/0.99      | v1_xboole_0(X2) = iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_4899,c_46,c_49,c_55,c_56,c_57]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5152,plain,
% 4.06/0.99      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 4.06/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | v1_funct_1(X1) != iProver_top
% 4.06/0.99      | v1_xboole_0(X2) = iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_5151]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5158,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 4.06/0.99      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 4.06/0.99      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 4.06/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | v1_funct_1(sK5) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top
% 4.06/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4993,c_5152]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_47,plain,
% 4.06/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_36,negated_conjecture,
% 4.06/0.99      ( v1_funct_2(sK5,sK3,sK2) ),
% 4.06/0.99      inference(cnf_transformation,[],[f103]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_53,plain,
% 4.06/0.99      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_54,plain,
% 4.06/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6000,plain,
% 4.06/0.99      ( v1_xboole_0(X0) = iProver_top
% 4.06/0.99      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 4.06/0.99      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_5158,c_47,c_52,c_53,c_54]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6001,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 4.06/0.99      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_6000]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6414,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 4.06/0.99      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_6262,c_6001]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6415,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 4.06/0.99      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_6414,c_4034]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6416,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 4.06/0.99      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK6,k1_xboole_0)
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_6415,c_6262]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6417,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 4.06/0.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_6416,c_4034]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6431,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 4.06/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 4.06/0.99      | v1_xboole_0(sK1)
% 4.06/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 4.06/0.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 4.06/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6417]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_26,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X3)
% 4.06/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X1)
% 4.06/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f118]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_251,plain,
% 4.06/0.99      ( ~ v1_funct_1(X3)
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X1)
% 4.06/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_26,c_30,c_29,c_28]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_252,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.06/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X3)
% 4.06/0.99      | v1_xboole_0(X1)
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | v1_xboole_0(X4)
% 4.06/0.99      | v1_xboole_0(X5)
% 4.06/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_251]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2493,plain,
% 4.06/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 4.06/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.06/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.06/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.06/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.06/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.06/0.99      | v1_funct_1(X2) != iProver_top
% 4.06/0.99      | v1_funct_1(X5) != iProver_top
% 4.06/0.99      | v1_xboole_0(X1) = iProver_top
% 4.06/0.99      | v1_xboole_0(X3) = iProver_top
% 4.06/0.99      | v1_xboole_0(X4) = iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4900,plain,
% 4.06/0.99      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 4.06/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 4.06/0.99      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | v1_funct_1(X1) != iProver_top
% 4.06/0.99      | v1_funct_1(sK6) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top
% 4.06/0.99      | v1_xboole_0(X2) = iProver_top
% 4.06/0.99      | v1_xboole_0(sK2) = iProver_top
% 4.06/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4895,c_2493]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6034,plain,
% 4.06/0.99      ( v1_funct_1(X1) != iProver_top
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 4.06/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 4.06/0.99      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top
% 4.06/0.99      | v1_xboole_0(X2) = iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_4900,c_46,c_49,c_55,c_56,c_57]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6035,plain,
% 4.06/0.99      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 4.06/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 4.06/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 4.06/0.99      | v1_funct_1(X1) != iProver_top
% 4.06/0.99      | v1_xboole_0(X2) = iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_6034]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6041,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 4.06/0.99      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 4.06/0.99      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 4.06/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | v1_funct_1(sK5) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top
% 4.06/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4993,c_6035]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6046,plain,
% 4.06/0.99      ( v1_xboole_0(X0) = iProver_top
% 4.06/0.99      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 4.06/0.99      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_6041,c_47,c_52,c_53,c_54]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6047,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 4.06/0.99      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_6046]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6413,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 4.06/0.99      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_6262,c_6047]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6418,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 4.06/0.99      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_6413,c_4034]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6419,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 4.06/0.99      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK6,k1_xboole_0)
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_6418,c_6262]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6420,plain,
% 4.06/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 4.06/0.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
% 4.06/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_6419,c_4034]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6432,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 4.06/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 4.06/0.99      | v1_xboole_0(sK1)
% 4.06/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 4.06/0.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 4.06/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6420]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7807,plain,
% 4.06/0.99      ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_6402,c_44,c_41,c_39,c_6431,c_6432]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_9,plain,
% 4.06/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f114]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2517,plain,
% 4.06/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_10,plain,
% 4.06/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2516,plain,
% 4.06/0.99      ( r1_tarski(X0,X1) != iProver_top
% 4.06/0.99      | r1_xboole_0(X0,X1) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4555,plain,
% 4.06/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.06/0.99      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2517,c_2516]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_813,plain,
% 4.06/0.99      ( ~ r1_tarski(X0,X1)
% 4.06/0.99      | v1_xboole_0(X0)
% 4.06/0.99      | k1_xboole_0 != X0
% 4.06/0.99      | k1_xboole_0 != X1 ),
% 4.06/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_9]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_814,plain,
% 4.06/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) ),
% 4.06/0.99      inference(unflattening,[status(thm)],[c_813]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f112]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_820,plain,
% 4.06/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 4.06/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_814,c_6]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_822,plain,
% 4.06/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5896,plain,
% 4.06/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4555,c_822]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f113]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2519,plain,
% 4.06/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4,plain,
% 4.06/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2521,plain,
% 4.06/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.06/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.06/0.99      | ~ r2_hidden(X2,X0)
% 4.06/0.99      | ~ v1_xboole_0(X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_430,plain,
% 4.06/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 4.06/0.99      inference(bin_hyper_res,[status(thm)],[c_14,c_339]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2491,plain,
% 4.06/0.99      ( r1_tarski(X0,X1) != iProver_top
% 4.06/0.99      | r2_hidden(X2,X0) != iProver_top
% 4.06/0.99      | v1_xboole_0(X1) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3794,plain,
% 4.06/0.99      ( r1_tarski(X0,X1) != iProver_top
% 4.06/0.99      | r1_xboole_0(X0,X2) = iProver_top
% 4.06/0.99      | v1_xboole_0(X1) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2521,c_2491]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6363,plain,
% 4.06/0.99      ( r1_xboole_0(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2519,c_3794]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_20,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | v1_partfun1(X0,X1)
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | v1_xboole_0(X2) ),
% 4.06/0.99      inference(cnf_transformation,[],[f85]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_19,plain,
% 4.06/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.06/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_23,plain,
% 4.06/0.99      ( ~ v1_partfun1(X0,X1)
% 4.06/0.99      | ~ v4_relat_1(X0,X1)
% 4.06/0.99      | ~ v1_relat_1(X0)
% 4.06/0.99      | k1_relat_1(X0) = X1 ),
% 4.06/0.99      inference(cnf_transformation,[],[f86]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_578,plain,
% 4.06/0.99      ( ~ v1_partfun1(X0,X1)
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ v1_relat_1(X0)
% 4.06/0.99      | k1_relat_1(X0) = X1 ),
% 4.06/0.99      inference(resolution,[status(thm)],[c_19,c_23]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_18,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_582,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ v1_partfun1(X0,X1)
% 4.06/0.99      | k1_relat_1(X0) = X1 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_578,c_23,c_19,c_18]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_583,plain,
% 4.06/0.99      ( ~ v1_partfun1(X0,X1)
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | k1_relat_1(X0) = X1 ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_582]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_654,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | k1_relat_1(X0) = X1 ),
% 4.06/0.99      inference(resolution,[status(thm)],[c_20,c_583]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_658,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | k1_relat_1(X0) = X1 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_654,c_23,c_20,c_19,c_18]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_659,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | v1_xboole_0(X2)
% 4.06/0.99      | k1_relat_1(X0) = X1 ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_658]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2489,plain,
% 4.06/0.99      ( k1_relat_1(X0) = X1
% 4.06/0.99      | v1_funct_2(X0,X1,X2) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.06/0.99      | v1_funct_1(X0) != iProver_top
% 4.06/0.99      | v1_xboole_0(X2) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3424,plain,
% 4.06/0.99      ( k1_relat_1(sK6) = sK4
% 4.06/0.99      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 4.06/0.99      | v1_funct_1(sK6) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2506,c_2489]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2692,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,sK2)
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | v1_xboole_0(sK2)
% 4.06/0.99      | k1_relat_1(X0) = X1 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_659]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2890,plain,
% 4.06/0.99      ( ~ v1_funct_2(sK6,X0,sK2)
% 4.06/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 4.06/0.99      | ~ v1_funct_1(sK6)
% 4.06/0.99      | v1_xboole_0(sK2)
% 4.06/0.99      | k1_relat_1(sK6) = X0 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_2692]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3275,plain,
% 4.06/0.99      ( ~ v1_funct_2(sK6,sK4,sK2)
% 4.06/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 4.06/0.99      | ~ v1_funct_1(sK6)
% 4.06/0.99      | v1_xboole_0(sK2)
% 4.06/0.99      | k1_relat_1(sK6) = sK4 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_2890]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3614,plain,
% 4.06/0.99      ( k1_relat_1(sK6) = sK4 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_3424,c_43,c_34,c_33,c_32,c_3275]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15,plain,
% 4.06/0.99      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 4.06/0.99      | ~ v1_relat_1(X1)
% 4.06/0.99      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2513,plain,
% 4.06/0.99      ( k7_relat_1(X0,X1) = k1_xboole_0
% 4.06/0.99      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 4.06/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4560,plain,
% 4.06/0.99      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 4.06/0.99      | r1_xboole_0(X0,sK4) != iProver_top
% 4.06/0.99      | v1_relat_1(sK6) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_3614,c_2513]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2512,plain,
% 4.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.06/0.99      | v1_relat_1(X0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4505,plain,
% 4.06/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2506,c_2512]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4724,plain,
% 4.06/0.99      ( r1_xboole_0(X0,sK4) != iProver_top | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 4.06/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4560,c_4505]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4725,plain,
% 4.06/0.99      ( k7_relat_1(sK6,X0) = k1_xboole_0 | r1_xboole_0(X0,sK4) != iProver_top ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_4724]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6394,plain,
% 4.06/0.99      ( k7_relat_1(sK6,X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_6363,c_4725]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7403,plain,
% 4.06/0.99      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_5896,c_6394]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3421,plain,
% 4.06/0.99      ( k1_relat_1(sK5) = sK3
% 4.06/0.99      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 4.06/0.99      | v1_funct_1(sK5) != iProver_top
% 4.06/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2503,c_2489]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2895,plain,
% 4.06/0.99      ( ~ v1_funct_2(sK5,X0,sK2)
% 4.06/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 4.06/0.99      | ~ v1_funct_1(sK5)
% 4.06/0.99      | v1_xboole_0(sK2)
% 4.06/0.99      | k1_relat_1(sK5) = X0 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_2692]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2897,plain,
% 4.06/0.99      ( ~ v1_funct_2(sK5,sK3,sK2)
% 4.06/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 4.06/0.99      | ~ v1_funct_1(sK5)
% 4.06/0.99      | v1_xboole_0(sK2)
% 4.06/0.99      | k1_relat_1(sK5) = sK3 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_2895]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3527,plain,
% 4.06/0.99      ( k1_relat_1(sK5) = sK3 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_3421,c_43,c_37,c_36,c_35,c_2897]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4561,plain,
% 4.06/0.99      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 4.06/0.99      | r1_xboole_0(X0,sK3) != iProver_top
% 4.06/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_3527,c_2513]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4506,plain,
% 4.06/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2503,c_2512]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5144,plain,
% 4.06/0.99      ( r1_xboole_0(X0,sK3) != iProver_top | k7_relat_1(sK5,X0) = k1_xboole_0 ),
% 4.06/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4561,c_4506]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5145,plain,
% 4.06/0.99      ( k7_relat_1(sK5,X0) = k1_xboole_0 | r1_xboole_0(X0,sK3) != iProver_top ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_5144]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_6395,plain,
% 4.06/0.99      ( k7_relat_1(sK5,X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_6363,c_5145]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7405,plain,
% 4.06/0.99      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_5896,c_6395]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7809,plain,
% 4.06/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 4.06/0.99      inference(light_normalisation,[status(thm)],[c_7807,c_7403,c_7405]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7810,plain,
% 4.06/0.99      ( $false ),
% 4.06/0.99      inference(equality_resolution_simp,[status(thm)],[c_7809]) ).
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  ------                               Statistics
% 4.06/0.99  
% 4.06/0.99  ------ General
% 4.06/0.99  
% 4.06/0.99  abstr_ref_over_cycles:                  0
% 4.06/0.99  abstr_ref_under_cycles:                 0
% 4.06/0.99  gc_basic_clause_elim:                   0
% 4.06/0.99  forced_gc_time:                         0
% 4.06/0.99  parsing_time:                           0.012
% 4.06/0.99  unif_index_cands_time:                  0.
% 4.06/0.99  unif_index_add_time:                    0.
% 4.06/0.99  orderings_time:                         0.
% 4.06/0.99  out_proof_time:                         0.018
% 4.06/0.99  total_time:                             0.392
% 4.06/0.99  num_of_symbols:                         60
% 4.06/0.99  num_of_terms:                           17294
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing
% 4.06/0.99  
% 4.06/0.99  num_of_splits:                          0
% 4.06/0.99  num_of_split_atoms:                     0
% 4.06/0.99  num_of_reused_defs:                     0
% 4.06/0.99  num_eq_ax_congr_red:                    35
% 4.06/0.99  num_of_sem_filtered_clauses:            1
% 4.06/0.99  num_of_subtypes:                        0
% 4.06/0.99  monotx_restored_types:                  0
% 4.06/0.99  sat_num_of_epr_types:                   0
% 4.06/0.99  sat_num_of_non_cyclic_types:            0
% 4.06/0.99  sat_guarded_non_collapsed_types:        0
% 4.06/0.99  num_pure_diseq_elim:                    0
% 4.06/0.99  simp_replaced_by:                       0
% 4.06/0.99  res_preprocessed:                       188
% 4.06/0.99  prep_upred:                             0
% 4.06/0.99  prep_unflattend:                        76
% 4.06/0.99  smt_new_axioms:                         0
% 4.06/0.99  pred_elim_cands:                        8
% 4.06/0.99  pred_elim:                              3
% 4.06/0.99  pred_elim_cl:                           5
% 4.06/0.99  pred_elim_cycles:                       7
% 4.06/0.99  merged_defs:                            16
% 4.06/0.99  merged_defs_ncl:                        0
% 4.06/0.99  bin_hyper_res:                          18
% 4.06/0.99  prep_cycles:                            4
% 4.06/0.99  pred_elim_time:                         0.013
% 4.06/0.99  splitting_time:                         0.
% 4.06/0.99  sem_filter_time:                        0.
% 4.06/0.99  monotx_time:                            0.
% 4.06/0.99  subtype_inf_time:                       0.
% 4.06/0.99  
% 4.06/0.99  ------ Problem properties
% 4.06/0.99  
% 4.06/0.99  clauses:                                38
% 4.06/0.99  conjectures:                            13
% 4.06/0.99  epr:                                    16
% 4.06/0.99  horn:                                   29
% 4.06/0.99  ground:                                 15
% 4.06/0.99  unary:                                  15
% 4.06/0.99  binary:                                 9
% 4.06/0.99  lits:                                   143
% 4.06/0.99  lits_eq:                                17
% 4.06/0.99  fd_pure:                                0
% 4.06/0.99  fd_pseudo:                              0
% 4.06/0.99  fd_cond:                                1
% 4.06/0.99  fd_pseudo_cond:                         2
% 4.06/0.99  ac_symbols:                             0
% 4.06/0.99  
% 4.06/0.99  ------ Propositional Solver
% 4.06/0.99  
% 4.06/0.99  prop_solver_calls:                      27
% 4.06/0.99  prop_fast_solver_calls:                 2098
% 4.06/0.99  smt_solver_calls:                       0
% 4.06/0.99  smt_fast_solver_calls:                  0
% 4.06/0.99  prop_num_of_clauses:                    3577
% 4.06/0.99  prop_preprocess_simplified:             9255
% 4.06/0.99  prop_fo_subsumed:                       93
% 4.06/0.99  prop_solver_time:                       0.
% 4.06/0.99  smt_solver_time:                        0.
% 4.06/0.99  smt_fast_solver_time:                   0.
% 4.06/0.99  prop_fast_solver_time:                  0.
% 4.06/0.99  prop_unsat_core_time:                   0.
% 4.06/0.99  
% 4.06/0.99  ------ QBF
% 4.06/0.99  
% 4.06/0.99  qbf_q_res:                              0
% 4.06/0.99  qbf_num_tautologies:                    0
% 4.06/0.99  qbf_prep_cycles:                        0
% 4.06/0.99  
% 4.06/0.99  ------ BMC1
% 4.06/0.99  
% 4.06/0.99  bmc1_current_bound:                     -1
% 4.06/0.99  bmc1_last_solved_bound:                 -1
% 4.06/0.99  bmc1_unsat_core_size:                   -1
% 4.06/0.99  bmc1_unsat_core_parents_size:           -1
% 4.06/0.99  bmc1_merge_next_fun:                    0
% 4.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.06/0.99  
% 4.06/0.99  ------ Instantiation
% 4.06/0.99  
% 4.06/0.99  inst_num_of_clauses:                    854
% 4.06/0.99  inst_num_in_passive:                    58
% 4.06/0.99  inst_num_in_active:                     524
% 4.06/0.99  inst_num_in_unprocessed:                272
% 4.06/0.99  inst_num_of_loops:                      530
% 4.06/0.99  inst_num_of_learning_restarts:          0
% 4.06/0.99  inst_num_moves_active_passive:          4
% 4.06/0.99  inst_lit_activity:                      0
% 4.06/0.99  inst_lit_activity_moves:                0
% 4.06/0.99  inst_num_tautologies:                   0
% 4.06/0.99  inst_num_prop_implied:                  0
% 4.06/0.99  inst_num_existing_simplified:           0
% 4.06/0.99  inst_num_eq_res_simplified:             0
% 4.06/0.99  inst_num_child_elim:                    0
% 4.06/0.99  inst_num_of_dismatching_blockings:      240
% 4.06/0.99  inst_num_of_non_proper_insts:           922
% 4.06/0.99  inst_num_of_duplicates:                 0
% 4.06/0.99  inst_inst_num_from_inst_to_res:         0
% 4.06/0.99  inst_dismatching_checking_time:         0.
% 4.06/0.99  
% 4.06/0.99  ------ Resolution
% 4.06/0.99  
% 4.06/0.99  res_num_of_clauses:                     0
% 4.06/0.99  res_num_in_passive:                     0
% 4.06/0.99  res_num_in_active:                      0
% 4.06/0.99  res_num_of_loops:                       192
% 4.06/0.99  res_forward_subset_subsumed:            23
% 4.06/0.99  res_backward_subset_subsumed:           0
% 4.06/0.99  res_forward_subsumed:                   0
% 4.06/0.99  res_backward_subsumed:                  0
% 4.06/0.99  res_forward_subsumption_resolution:     2
% 4.06/0.99  res_backward_subsumption_resolution:    0
% 4.06/0.99  res_clause_to_clause_subsumption:       493
% 4.06/0.99  res_orphan_elimination:                 0
% 4.06/0.99  res_tautology_del:                      46
% 4.06/0.99  res_num_eq_res_simplified:              0
% 4.06/0.99  res_num_sel_changes:                    0
% 4.06/0.99  res_moves_from_active_to_pass:          0
% 4.06/0.99  
% 4.06/0.99  ------ Superposition
% 4.06/0.99  
% 4.06/0.99  sup_time_total:                         0.
% 4.06/0.99  sup_time_generating:                    0.
% 4.06/0.99  sup_time_sim_full:                      0.
% 4.06/0.99  sup_time_sim_immed:                     0.
% 4.06/0.99  
% 4.06/0.99  sup_num_of_clauses:                     172
% 4.06/0.99  sup_num_in_active:                      102
% 4.06/0.99  sup_num_in_passive:                     70
% 4.06/0.99  sup_num_of_loops:                       105
% 4.06/0.99  sup_fw_superposition:                   101
% 4.06/0.99  sup_bw_superposition:                   82
% 4.06/0.99  sup_immediate_simplified:               85
% 4.06/0.99  sup_given_eliminated:                   0
% 4.06/0.99  comparisons_done:                       0
% 4.06/0.99  comparisons_avoided:                    0
% 4.06/0.99  
% 4.06/0.99  ------ Simplifications
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  sim_fw_subset_subsumed:                 10
% 4.06/0.99  sim_bw_subset_subsumed:                 0
% 4.06/0.99  sim_fw_subsumed:                        6
% 4.06/0.99  sim_bw_subsumed:                        2
% 4.06/0.99  sim_fw_subsumption_res:                 0
% 4.06/0.99  sim_bw_subsumption_res:                 0
% 4.06/0.99  sim_tautology_del:                      4
% 4.06/0.99  sim_eq_tautology_del:                   2
% 4.06/0.99  sim_eq_res_simp:                        0
% 4.06/0.99  sim_fw_demodulated:                     46
% 4.06/0.99  sim_bw_demodulated:                     3
% 4.06/0.99  sim_light_normalised:                   34
% 4.06/0.99  sim_joinable_taut:                      0
% 4.06/0.99  sim_joinable_simp:                      0
% 4.06/0.99  sim_ac_normalised:                      0
% 4.06/0.99  sim_smt_subsumption:                    0
% 4.06/0.99  
%------------------------------------------------------------------------------
