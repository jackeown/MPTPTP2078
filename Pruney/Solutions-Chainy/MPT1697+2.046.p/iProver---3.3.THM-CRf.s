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
% DateTime   : Thu Dec  3 12:21:32 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  229 (1655 expanded)
%              Number of clauses        :  140 ( 398 expanded)
%              Number of leaves         :   22 ( 609 expanded)
%              Depth                    :   24
%              Number of atoms          : 1204 (19189 expanded)
%              Number of equality atoms :  425 (4405 expanded)
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f54,f53,f52,f51,f50,f49])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f104,plain,(
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
    inference(equality_resolution,[],[f78])).

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

fof(f81,plain,(
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

fof(f82,plain,(
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

fof(f83,plain,(
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

fof(f85,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f18,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2107,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2121,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3539,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2107,c_2121])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_311,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_312,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_396,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_312])).

cnf(c_2099,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_5946,plain,
    ( k9_subset_1(sK1,X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_3539,c_2099])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2110,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2118,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5084,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2110,c_2118])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2550,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2706,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2550])).

cnf(c_5538,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5084,c_34,c_32,c_2706])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2113,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5083,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_2118])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2545,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2700,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_5356,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5083,c_31,c_29,c_2700])).

cnf(c_28,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_5360,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_5356,c_28])).

cnf(c_5542,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_5538,c_5360])).

cnf(c_6515,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_5946,c_5542])).

cnf(c_14,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_597,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_598,plain,
    ( r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_600,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_39,c_37])).

cnf(c_2098,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2128,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3001,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2098,c_2128])).

cnf(c_6516,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6515,c_3001])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f87])).

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
    inference(cnf_transformation,[],[f104])).

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
    inference(cnf_transformation,[],[f81])).

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
    inference(cnf_transformation,[],[f82])).

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
    inference(cnf_transformation,[],[f83])).

cnf(c_226,plain,
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

cnf(c_227,plain,
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
    inference(renaming,[status(thm)],[c_226])).

cnf(c_2101,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_5361,plain,
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
    inference(superposition,[status(thm)],[c_5356,c_2101])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_43,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_46,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_52,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_53,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_54,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5721,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5361,c_43,c_46,c_52,c_53,c_54])).

cnf(c_5722,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5721])).

cnf(c_5737,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5538,c_5722])).

cnf(c_44,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_50,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5861,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5737,c_44,c_49,c_50,c_51])).

cnf(c_5862,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5861])).

cnf(c_6524,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5946,c_5862])).

cnf(c_6530,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6524,c_3001])).

cnf(c_6531,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6530,c_5946])).

cnf(c_6532,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6531,c_3001])).

cnf(c_6698,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6532])).

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
    inference(cnf_transformation,[],[f103])).

cnf(c_233,plain,
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

cnf(c_234,plain,
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
    inference(renaming,[status(thm)],[c_233])).

cnf(c_2100,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_5362,plain,
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
    inference(superposition,[status(thm)],[c_5356,c_2100])).

cnf(c_7271,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5362,c_43,c_46,c_52,c_53,c_54])).

cnf(c_7272,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7271])).

cnf(c_7287,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5538,c_7272])).

cnf(c_7404,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7287,c_44,c_49,c_50,c_51])).

cnf(c_7405,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7404])).

cnf(c_7415,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5946,c_7405])).

cnf(c_7435,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7415,c_3001])).

cnf(c_7436,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7435,c_5946])).

cnf(c_7437,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7436,c_3001])).

cnf(c_7444,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7437])).

cnf(c_10201,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6516,c_41,c_38,c_36,c_6698,c_7444])).

cnf(c_8,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2129,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3457,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2129])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2126,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2125,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2127,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5063,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2125,c_2127])).

cnf(c_7734,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2126,c_5063])).

cnf(c_7749,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3457,c_7734])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_534,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_16,c_20])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_20,c_16,c_15])).

cnf(c_539,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_610,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_17,c_539])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_20,c_17,c_16,c_15])).

cnf(c_615,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_614])).

cnf(c_2097,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_2856,plain,
    ( k1_relat_1(sK6) = sK4
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_2097])).

cnf(c_2555,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X1)
    | k1_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_2715,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | k1_relat_1(sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_2555])).

cnf(c_2995,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2856,c_40,c_31,c_30,c_29,c_2715])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2120,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4028,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2995,c_2120])).

cnf(c_2494,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2495,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2494])).

cnf(c_4211,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4028,c_54,c_2495])).

cnf(c_4212,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4211])).

cnf(c_7799,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7749,c_4212])).

cnf(c_2852,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2110,c_2097])).

cnf(c_2560,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1)
    | k1_relat_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_2718,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2560])).

cnf(c_2905,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2852,c_40,c_34,c_33,c_32,c_2718])).

cnf(c_4029,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_2120])).

cnf(c_2497,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2498,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2497])).

cnf(c_4693,plain,
    ( r1_xboole_0(X0,sK3) != iProver_top
    | k7_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4029,c_51,c_2498])).

cnf(c_4694,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4693])).

cnf(c_7800,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7749,c_4694])).

cnf(c_10203,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10201,c_7799,c_7800])).

cnf(c_10204,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10203])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    --mode clausify
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/1.00  --prep_def_merge_mbd                    true
% 3.79/1.00  --prep_def_merge_tr_red                 false
% 3.79/1.00  --prep_def_merge_tr_cl                  false
% 3.79/1.00  --smt_preprocessing                     true
% 3.79/1.00  --smt_ac_axioms                         fast
% 3.79/1.00  --preprocessed_out                      false
% 3.79/1.00  --preprocessed_stats                    false
% 3.79/1.00  
% 3.79/1.00  ------ Abstraction refinement Options
% 3.79/1.00  
% 3.79/1.00  --abstr_ref                             []
% 3.79/1.00  --abstr_ref_prep                        false
% 3.79/1.00  --abstr_ref_until_sat                   false
% 3.79/1.00  --abstr_ref_sig_restrict                funpre
% 3.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/1.00  --abstr_ref_under                       []
% 3.79/1.00  
% 3.79/1.00  ------ SAT Options
% 3.79/1.00  
% 3.79/1.00  --sat_mode                              false
% 3.79/1.00  --sat_fm_restart_options                ""
% 3.79/1.00  --sat_gr_def                            false
% 3.79/1.00  --sat_epr_types                         true
% 3.79/1.00  --sat_non_cyclic_types                  false
% 3.79/1.00  --sat_finite_models                     false
% 3.79/1.00  --sat_fm_lemmas                         false
% 3.79/1.00  --sat_fm_prep                           false
% 3.79/1.00  --sat_fm_uc_incr                        true
% 3.79/1.00  --sat_out_model                         small
% 3.79/1.00  --sat_out_clauses                       false
% 3.79/1.00  
% 3.79/1.00  ------ QBF Options
% 3.79/1.00  
% 3.79/1.00  --qbf_mode                              false
% 3.79/1.00  --qbf_elim_univ                         false
% 3.79/1.00  --qbf_dom_inst                          none
% 3.79/1.00  --qbf_dom_pre_inst                      false
% 3.79/1.00  --qbf_sk_in                             false
% 3.79/1.00  --qbf_pred_elim                         true
% 3.79/1.00  --qbf_split                             512
% 3.79/1.00  
% 3.79/1.00  ------ BMC1 Options
% 3.79/1.00  
% 3.79/1.00  --bmc1_incremental                      false
% 3.79/1.00  --bmc1_axioms                           reachable_all
% 3.79/1.00  --bmc1_min_bound                        0
% 3.79/1.00  --bmc1_max_bound                        -1
% 3.79/1.00  --bmc1_max_bound_default                -1
% 3.79/1.00  --bmc1_symbol_reachability              true
% 3.79/1.00  --bmc1_property_lemmas                  false
% 3.79/1.00  --bmc1_k_induction                      false
% 3.79/1.00  --bmc1_non_equiv_states                 false
% 3.79/1.00  --bmc1_deadlock                         false
% 3.79/1.00  --bmc1_ucm                              false
% 3.79/1.00  --bmc1_add_unsat_core                   none
% 3.79/1.00  --bmc1_unsat_core_children              false
% 3.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/1.00  --bmc1_out_stat                         full
% 3.79/1.00  --bmc1_ground_init                      false
% 3.79/1.00  --bmc1_pre_inst_next_state              false
% 3.79/1.00  --bmc1_pre_inst_state                   false
% 3.79/1.00  --bmc1_pre_inst_reach_state             false
% 3.79/1.00  --bmc1_out_unsat_core                   false
% 3.79/1.00  --bmc1_aig_witness_out                  false
% 3.79/1.00  --bmc1_verbose                          false
% 3.79/1.00  --bmc1_dump_clauses_tptp                false
% 3.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.79/1.00  --bmc1_dump_file                        -
% 3.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.79/1.00  --bmc1_ucm_extend_mode                  1
% 3.79/1.00  --bmc1_ucm_init_mode                    2
% 3.79/1.00  --bmc1_ucm_cone_mode                    none
% 3.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.79/1.00  --bmc1_ucm_relax_model                  4
% 3.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/1.00  --bmc1_ucm_layered_model                none
% 3.79/1.00  --bmc1_ucm_max_lemma_size               10
% 3.79/1.00  
% 3.79/1.00  ------ AIG Options
% 3.79/1.00  
% 3.79/1.00  --aig_mode                              false
% 3.79/1.00  
% 3.79/1.00  ------ Instantiation Options
% 3.79/1.00  
% 3.79/1.00  --instantiation_flag                    true
% 3.79/1.00  --inst_sos_flag                         false
% 3.79/1.00  --inst_sos_phase                        true
% 3.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/1.00  --inst_lit_sel_side                     num_symb
% 3.79/1.00  --inst_solver_per_active                1400
% 3.79/1.00  --inst_solver_calls_frac                1.
% 3.79/1.00  --inst_passive_queue_type               priority_queues
% 3.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/1.00  --inst_passive_queues_freq              [25;2]
% 3.79/1.00  --inst_dismatching                      true
% 3.79/1.00  --inst_eager_unprocessed_to_passive     true
% 3.79/1.00  --inst_prop_sim_given                   true
% 3.79/1.00  --inst_prop_sim_new                     false
% 3.79/1.00  --inst_subs_new                         false
% 3.79/1.00  --inst_eq_res_simp                      false
% 3.79/1.00  --inst_subs_given                       false
% 3.79/1.00  --inst_orphan_elimination               true
% 3.79/1.00  --inst_learning_loop_flag               true
% 3.79/1.00  --inst_learning_start                   3000
% 3.79/1.00  --inst_learning_factor                  2
% 3.79/1.00  --inst_start_prop_sim_after_learn       3
% 3.79/1.00  --inst_sel_renew                        solver
% 3.79/1.00  --inst_lit_activity_flag                true
% 3.79/1.00  --inst_restr_to_given                   false
% 3.79/1.00  --inst_activity_threshold               500
% 3.79/1.00  --inst_out_proof                        true
% 3.79/1.00  
% 3.79/1.00  ------ Resolution Options
% 3.79/1.00  
% 3.79/1.00  --resolution_flag                       true
% 3.79/1.00  --res_lit_sel                           adaptive
% 3.79/1.00  --res_lit_sel_side                      none
% 3.79/1.00  --res_ordering                          kbo
% 3.79/1.00  --res_to_prop_solver                    active
% 3.79/1.00  --res_prop_simpl_new                    false
% 3.79/1.00  --res_prop_simpl_given                  true
% 3.79/1.00  --res_passive_queue_type                priority_queues
% 3.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/1.00  --res_passive_queues_freq               [15;5]
% 3.79/1.00  --res_forward_subs                      full
% 3.79/1.00  --res_backward_subs                     full
% 3.79/1.00  --res_forward_subs_resolution           true
% 3.79/1.00  --res_backward_subs_resolution          true
% 3.79/1.00  --res_orphan_elimination                true
% 3.79/1.00  --res_time_limit                        2.
% 3.79/1.00  --res_out_proof                         true
% 3.79/1.00  
% 3.79/1.00  ------ Superposition Options
% 3.79/1.00  
% 3.79/1.00  --superposition_flag                    true
% 3.79/1.00  --sup_passive_queue_type                priority_queues
% 3.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.79/1.00  --demod_completeness_check              fast
% 3.79/1.00  --demod_use_ground                      true
% 3.79/1.00  --sup_to_prop_solver                    passive
% 3.79/1.00  --sup_prop_simpl_new                    true
% 3.79/1.00  --sup_prop_simpl_given                  true
% 3.79/1.00  --sup_fun_splitting                     false
% 3.79/1.00  --sup_smt_interval                      50000
% 3.79/1.00  
% 3.79/1.00  ------ Superposition Simplification Setup
% 3.79/1.00  
% 3.79/1.00  --sup_indices_passive                   []
% 3.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_full_bw                           [BwDemod]
% 3.79/1.00  --sup_immed_triv                        [TrivRules]
% 3.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_immed_bw_main                     []
% 3.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.00  
% 3.79/1.00  ------ Combination Options
% 3.79/1.00  
% 3.79/1.00  --comb_res_mult                         3
% 3.79/1.00  --comb_sup_mult                         2
% 3.79/1.00  --comb_inst_mult                        10
% 3.79/1.00  
% 3.79/1.00  ------ Debug Options
% 3.79/1.00  
% 3.79/1.00  --dbg_backtrace                         false
% 3.79/1.00  --dbg_dump_prop_clauses                 false
% 3.79/1.00  --dbg_dump_prop_clauses_file            -
% 3.79/1.00  --dbg_out_stat                          false
% 3.79/1.00  ------ Parsing...
% 3.79/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.00  ------ Proving...
% 3.79/1.00  ------ Problem Properties 
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  clauses                                 35
% 3.79/1.00  conjectures                             13
% 3.79/1.00  EPR                                     12
% 3.79/1.00  Horn                                    26
% 3.79/1.00  unary                                   15
% 3.79/1.00  binary                                  8
% 3.79/1.00  lits                                    135
% 3.79/1.00  lits eq                                 17
% 3.79/1.00  fd_pure                                 0
% 3.79/1.00  fd_pseudo                               0
% 3.79/1.00  fd_cond                                 0
% 3.79/1.00  fd_pseudo_cond                          2
% 3.79/1.00  AC symbols                              0
% 3.79/1.00  
% 3.79/1.00  ------ Schedule dynamic 5 is on 
% 3.79/1.00  
% 3.79/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  ------ 
% 3.79/1.00  Current options:
% 3.79/1.00  ------ 
% 3.79/1.00  
% 3.79/1.00  ------ Input Options
% 3.79/1.00  
% 3.79/1.00  --out_options                           all
% 3.79/1.00  --tptp_safe_out                         true
% 3.79/1.00  --problem_path                          ""
% 3.79/1.00  --include_path                          ""
% 3.79/1.00  --clausifier                            res/vclausify_rel
% 3.79/1.00  --clausifier_options                    --mode clausify
% 3.79/1.00  --stdin                                 false
% 3.79/1.00  --stats_out                             all
% 3.79/1.00  
% 3.79/1.00  ------ General Options
% 3.79/1.00  
% 3.79/1.00  --fof                                   false
% 3.79/1.00  --time_out_real                         305.
% 3.79/1.00  --time_out_virtual                      -1.
% 3.79/1.00  --symbol_type_check                     false
% 3.79/1.00  --clausify_out                          false
% 3.79/1.00  --sig_cnt_out                           false
% 3.79/1.00  --trig_cnt_out                          false
% 3.79/1.00  --trig_cnt_out_tolerance                1.
% 3.79/1.00  --trig_cnt_out_sk_spl                   false
% 3.79/1.00  --abstr_cl_out                          false
% 3.79/1.00  
% 3.79/1.00  ------ Global Options
% 3.79/1.00  
% 3.79/1.00  --schedule                              default
% 3.79/1.00  --add_important_lit                     false
% 3.79/1.00  --prop_solver_per_cl                    1000
% 3.79/1.00  --min_unsat_core                        false
% 3.79/1.00  --soft_assumptions                      false
% 3.79/1.00  --soft_lemma_size                       3
% 3.79/1.00  --prop_impl_unit_size                   0
% 3.79/1.00  --prop_impl_unit                        []
% 3.79/1.00  --share_sel_clauses                     true
% 3.79/1.00  --reset_solvers                         false
% 3.79/1.00  --bc_imp_inh                            [conj_cone]
% 3.79/1.00  --conj_cone_tolerance                   3.
% 3.79/1.00  --extra_neg_conj                        none
% 3.79/1.00  --large_theory_mode                     true
% 3.79/1.00  --prolific_symb_bound                   200
% 3.79/1.00  --lt_threshold                          2000
% 3.79/1.00  --clause_weak_htbl                      true
% 3.79/1.00  --gc_record_bc_elim                     false
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing Options
% 3.79/1.00  
% 3.79/1.00  --preprocessing_flag                    true
% 3.79/1.00  --time_out_prep_mult                    0.1
% 3.79/1.00  --splitting_mode                        input
% 3.79/1.00  --splitting_grd                         true
% 3.79/1.00  --splitting_cvd                         false
% 3.79/1.00  --splitting_cvd_svl                     false
% 3.79/1.00  --splitting_nvd                         32
% 3.79/1.00  --sub_typing                            true
% 3.79/1.00  --prep_gs_sim                           true
% 3.79/1.00  --prep_unflatten                        true
% 3.79/1.00  --prep_res_sim                          true
% 3.79/1.00  --prep_upred                            true
% 3.79/1.00  --prep_sem_filter                       exhaustive
% 3.79/1.00  --prep_sem_filter_out                   false
% 3.79/1.00  --pred_elim                             true
% 3.79/1.00  --res_sim_input                         true
% 3.79/1.00  --eq_ax_congr_red                       true
% 3.79/1.00  --pure_diseq_elim                       true
% 3.79/1.00  --brand_transform                       false
% 3.79/1.00  --non_eq_to_eq                          false
% 3.79/1.00  --prep_def_merge                        true
% 3.79/1.00  --prep_def_merge_prop_impl              false
% 3.79/1.00  --prep_def_merge_mbd                    true
% 3.79/1.00  --prep_def_merge_tr_red                 false
% 3.79/1.00  --prep_def_merge_tr_cl                  false
% 3.79/1.00  --smt_preprocessing                     true
% 3.79/1.00  --smt_ac_axioms                         fast
% 3.79/1.00  --preprocessed_out                      false
% 3.79/1.00  --preprocessed_stats                    false
% 3.79/1.00  
% 3.79/1.00  ------ Abstraction refinement Options
% 3.79/1.00  
% 3.79/1.00  --abstr_ref                             []
% 3.79/1.00  --abstr_ref_prep                        false
% 3.79/1.00  --abstr_ref_until_sat                   false
% 3.79/1.00  --abstr_ref_sig_restrict                funpre
% 3.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/1.00  --abstr_ref_under                       []
% 3.79/1.00  
% 3.79/1.00  ------ SAT Options
% 3.79/1.00  
% 3.79/1.00  --sat_mode                              false
% 3.79/1.00  --sat_fm_restart_options                ""
% 3.79/1.00  --sat_gr_def                            false
% 3.79/1.00  --sat_epr_types                         true
% 3.79/1.00  --sat_non_cyclic_types                  false
% 3.79/1.00  --sat_finite_models                     false
% 3.79/1.00  --sat_fm_lemmas                         false
% 3.79/1.00  --sat_fm_prep                           false
% 3.79/1.00  --sat_fm_uc_incr                        true
% 3.79/1.00  --sat_out_model                         small
% 3.79/1.00  --sat_out_clauses                       false
% 3.79/1.00  
% 3.79/1.00  ------ QBF Options
% 3.79/1.00  
% 3.79/1.00  --qbf_mode                              false
% 3.79/1.00  --qbf_elim_univ                         false
% 3.79/1.00  --qbf_dom_inst                          none
% 3.79/1.00  --qbf_dom_pre_inst                      false
% 3.79/1.00  --qbf_sk_in                             false
% 3.79/1.00  --qbf_pred_elim                         true
% 3.79/1.00  --qbf_split                             512
% 3.79/1.00  
% 3.79/1.00  ------ BMC1 Options
% 3.79/1.00  
% 3.79/1.00  --bmc1_incremental                      false
% 3.79/1.00  --bmc1_axioms                           reachable_all
% 3.79/1.00  --bmc1_min_bound                        0
% 3.79/1.00  --bmc1_max_bound                        -1
% 3.79/1.00  --bmc1_max_bound_default                -1
% 3.79/1.00  --bmc1_symbol_reachability              true
% 3.79/1.00  --bmc1_property_lemmas                  false
% 3.79/1.00  --bmc1_k_induction                      false
% 3.79/1.00  --bmc1_non_equiv_states                 false
% 3.79/1.00  --bmc1_deadlock                         false
% 3.79/1.00  --bmc1_ucm                              false
% 3.79/1.00  --bmc1_add_unsat_core                   none
% 3.79/1.00  --bmc1_unsat_core_children              false
% 3.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/1.00  --bmc1_out_stat                         full
% 3.79/1.00  --bmc1_ground_init                      false
% 3.79/1.00  --bmc1_pre_inst_next_state              false
% 3.79/1.00  --bmc1_pre_inst_state                   false
% 3.79/1.00  --bmc1_pre_inst_reach_state             false
% 3.79/1.00  --bmc1_out_unsat_core                   false
% 3.79/1.00  --bmc1_aig_witness_out                  false
% 3.79/1.00  --bmc1_verbose                          false
% 3.79/1.00  --bmc1_dump_clauses_tptp                false
% 3.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.79/1.00  --bmc1_dump_file                        -
% 3.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.79/1.00  --bmc1_ucm_extend_mode                  1
% 3.79/1.00  --bmc1_ucm_init_mode                    2
% 3.79/1.00  --bmc1_ucm_cone_mode                    none
% 3.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.79/1.00  --bmc1_ucm_relax_model                  4
% 3.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/1.00  --bmc1_ucm_layered_model                none
% 3.79/1.00  --bmc1_ucm_max_lemma_size               10
% 3.79/1.00  
% 3.79/1.00  ------ AIG Options
% 3.79/1.00  
% 3.79/1.00  --aig_mode                              false
% 3.79/1.00  
% 3.79/1.00  ------ Instantiation Options
% 3.79/1.00  
% 3.79/1.00  --instantiation_flag                    true
% 3.79/1.00  --inst_sos_flag                         false
% 3.79/1.00  --inst_sos_phase                        true
% 3.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/1.00  --inst_lit_sel_side                     none
% 3.79/1.00  --inst_solver_per_active                1400
% 3.79/1.00  --inst_solver_calls_frac                1.
% 3.79/1.00  --inst_passive_queue_type               priority_queues
% 3.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/1.00  --inst_passive_queues_freq              [25;2]
% 3.79/1.00  --inst_dismatching                      true
% 3.79/1.00  --inst_eager_unprocessed_to_passive     true
% 3.79/1.00  --inst_prop_sim_given                   true
% 3.79/1.00  --inst_prop_sim_new                     false
% 3.79/1.00  --inst_subs_new                         false
% 3.79/1.00  --inst_eq_res_simp                      false
% 3.79/1.00  --inst_subs_given                       false
% 3.79/1.00  --inst_orphan_elimination               true
% 3.79/1.00  --inst_learning_loop_flag               true
% 3.79/1.00  --inst_learning_start                   3000
% 3.79/1.00  --inst_learning_factor                  2
% 3.79/1.00  --inst_start_prop_sim_after_learn       3
% 3.79/1.00  --inst_sel_renew                        solver
% 3.79/1.00  --inst_lit_activity_flag                true
% 3.79/1.00  --inst_restr_to_given                   false
% 3.79/1.00  --inst_activity_threshold               500
% 3.79/1.00  --inst_out_proof                        true
% 3.79/1.00  
% 3.79/1.00  ------ Resolution Options
% 3.79/1.00  
% 3.79/1.00  --resolution_flag                       false
% 3.79/1.00  --res_lit_sel                           adaptive
% 3.79/1.00  --res_lit_sel_side                      none
% 3.79/1.00  --res_ordering                          kbo
% 3.79/1.00  --res_to_prop_solver                    active
% 3.79/1.00  --res_prop_simpl_new                    false
% 3.79/1.00  --res_prop_simpl_given                  true
% 3.79/1.00  --res_passive_queue_type                priority_queues
% 3.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/1.00  --res_passive_queues_freq               [15;5]
% 3.79/1.00  --res_forward_subs                      full
% 3.79/1.00  --res_backward_subs                     full
% 3.79/1.00  --res_forward_subs_resolution           true
% 3.79/1.00  --res_backward_subs_resolution          true
% 3.79/1.00  --res_orphan_elimination                true
% 3.79/1.00  --res_time_limit                        2.
% 3.79/1.00  --res_out_proof                         true
% 3.79/1.00  
% 3.79/1.00  ------ Superposition Options
% 3.79/1.00  
% 3.79/1.00  --superposition_flag                    true
% 3.79/1.00  --sup_passive_queue_type                priority_queues
% 3.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.79/1.00  --demod_completeness_check              fast
% 3.79/1.00  --demod_use_ground                      true
% 3.79/1.00  --sup_to_prop_solver                    passive
% 3.79/1.00  --sup_prop_simpl_new                    true
% 3.79/1.00  --sup_prop_simpl_given                  true
% 3.79/1.00  --sup_fun_splitting                     false
% 3.79/1.00  --sup_smt_interval                      50000
% 3.79/1.00  
% 3.79/1.00  ------ Superposition Simplification Setup
% 3.79/1.00  
% 3.79/1.00  --sup_indices_passive                   []
% 3.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_full_bw                           [BwDemod]
% 3.79/1.00  --sup_immed_triv                        [TrivRules]
% 3.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_immed_bw_main                     []
% 3.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.00  
% 3.79/1.00  ------ Combination Options
% 3.79/1.00  
% 3.79/1.00  --comb_res_mult                         3
% 3.79/1.00  --comb_sup_mult                         2
% 3.79/1.00  --comb_inst_mult                        10
% 3.79/1.00  
% 3.79/1.00  ------ Debug Options
% 3.79/1.00  
% 3.79/1.00  --dbg_backtrace                         false
% 3.79/1.00  --dbg_dump_prop_clauses                 false
% 3.79/1.00  --dbg_dump_prop_clauses_file            -
% 3.79/1.00  --dbg_out_stat                          false
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  ------ Proving...
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  % SZS status Theorem for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00   Resolution empty clause
% 3.79/1.00  
% 3.79/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  fof(f16,conjecture,(
% 3.79/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f17,negated_conjecture,(
% 3.79/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.79/1.00    inference(negated_conjecture,[],[f16])).
% 3.79/1.00  
% 3.79/1.00  fof(f37,plain,(
% 3.79/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.79/1.00    inference(ennf_transformation,[],[f17])).
% 3.79/1.00  
% 3.79/1.00  fof(f38,plain,(
% 3.79/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.79/1.00    inference(flattening,[],[f37])).
% 3.79/1.00  
% 3.79/1.00  fof(f54,plain,(
% 3.79/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f53,plain,(
% 3.79/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f52,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f51,plain,(
% 3.79/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f50,plain,(
% 3.79/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f49,plain,(
% 3.79/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f55,plain,(
% 3.79/1.00    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f54,f53,f52,f51,f50,f49])).
% 3.79/1.00  
% 3.79/1.00  fof(f89,plain,(
% 3.79/1.00    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f6,axiom,(
% 3.79/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f44,plain,(
% 3.79/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.79/1.00    inference(nnf_transformation,[],[f6])).
% 3.79/1.00  
% 3.79/1.00  fof(f66,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f44])).
% 3.79/1.00  
% 3.79/1.00  fof(f5,axiom,(
% 3.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f21,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.79/1.00    inference(ennf_transformation,[],[f5])).
% 3.79/1.00  
% 3.79/1.00  fof(f65,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f21])).
% 3.79/1.00  
% 3.79/1.00  fof(f67,plain,(
% 3.79/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f44])).
% 3.79/1.00  
% 3.79/1.00  fof(f93,plain,(
% 3.79/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f13,axiom,(
% 3.79/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f31,plain,(
% 3.79/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.79/1.00    inference(ennf_transformation,[],[f13])).
% 3.79/1.00  
% 3.79/1.00  fof(f32,plain,(
% 3.79/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.79/1.00    inference(flattening,[],[f31])).
% 3.79/1.00  
% 3.79/1.00  fof(f77,plain,(
% 3.79/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f32])).
% 3.79/1.00  
% 3.79/1.00  fof(f91,plain,(
% 3.79/1.00    v1_funct_1(sK5)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f96,plain,(
% 3.79/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f94,plain,(
% 3.79/1.00    v1_funct_1(sK6)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f97,plain,(
% 3.79/1.00    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f8,axiom,(
% 3.79/1.00    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f23,plain,(
% 3.79/1.00    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.79/1.00    inference(ennf_transformation,[],[f8])).
% 3.79/1.00  
% 3.79/1.00  fof(f24,plain,(
% 3.79/1.00    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.79/1.00    inference(flattening,[],[f23])).
% 3.79/1.00  
% 3.79/1.00  fof(f45,plain,(
% 3.79/1.00    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.79/1.00    inference(nnf_transformation,[],[f24])).
% 3.79/1.00  
% 3.79/1.00  fof(f69,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f45])).
% 3.79/1.00  
% 3.79/1.00  fof(f90,plain,(
% 3.79/1.00    r1_subset_1(sK3,sK4)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f86,plain,(
% 3.79/1.00    ~v1_xboole_0(sK3)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f88,plain,(
% 3.79/1.00    ~v1_xboole_0(sK4)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f1,axiom,(
% 3.79/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f39,plain,(
% 3.79/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.79/1.00    inference(nnf_transformation,[],[f1])).
% 3.79/1.00  
% 3.79/1.00  fof(f56,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f39])).
% 3.79/1.00  
% 3.79/1.00  fof(f84,plain,(
% 3.79/1.00    ~v1_xboole_0(sK1)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f87,plain,(
% 3.79/1.00    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f14,axiom,(
% 3.79/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f33,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.79/1.00    inference(ennf_transformation,[],[f14])).
% 3.79/1.00  
% 3.79/1.00  fof(f34,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.79/1.00    inference(flattening,[],[f33])).
% 3.79/1.00  
% 3.79/1.00  fof(f47,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.79/1.00    inference(nnf_transformation,[],[f34])).
% 3.79/1.00  
% 3.79/1.00  fof(f48,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.79/1.00    inference(flattening,[],[f47])).
% 3.79/1.00  
% 3.79/1.00  fof(f78,plain,(
% 3.79/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f48])).
% 3.79/1.00  
% 3.79/1.00  fof(f104,plain,(
% 3.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(equality_resolution,[],[f78])).
% 3.79/1.00  
% 3.79/1.00  fof(f15,axiom,(
% 3.79/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f35,plain,(
% 3.79/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.79/1.00    inference(ennf_transformation,[],[f15])).
% 3.79/1.00  
% 3.79/1.00  fof(f36,plain,(
% 3.79/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.79/1.00    inference(flattening,[],[f35])).
% 3.79/1.00  
% 3.79/1.00  fof(f81,plain,(
% 3.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f36])).
% 3.79/1.00  
% 3.79/1.00  fof(f82,plain,(
% 3.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f36])).
% 3.79/1.00  
% 3.79/1.00  fof(f83,plain,(
% 3.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f36])).
% 3.79/1.00  
% 3.79/1.00  fof(f85,plain,(
% 3.79/1.00    ~v1_xboole_0(sK2)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f95,plain,(
% 3.79/1.00    v1_funct_2(sK6,sK4,sK2)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f92,plain,(
% 3.79/1.00    v1_funct_2(sK5,sK3,sK2)),
% 3.79/1.00    inference(cnf_transformation,[],[f55])).
% 3.79/1.00  
% 3.79/1.00  fof(f79,plain,(
% 3.79/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f48])).
% 3.79/1.00  
% 3.79/1.00  fof(f103,plain,(
% 3.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(equality_resolution,[],[f79])).
% 3.79/1.00  
% 3.79/1.00  fof(f4,axiom,(
% 3.79/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f64,plain,(
% 3.79/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.79/1.00    inference(cnf_transformation,[],[f4])).
% 3.79/1.00  
% 3.79/1.00  fof(f57,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.79/1.00    inference(cnf_transformation,[],[f39])).
% 3.79/1.00  
% 3.79/1.00  fof(f2,axiom,(
% 3.79/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f18,plain,(
% 3.79/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.79/1.00    inference(rectify,[],[f2])).
% 3.79/1.00  
% 3.79/1.00  fof(f20,plain,(
% 3.79/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.79/1.00    inference(ennf_transformation,[],[f18])).
% 3.79/1.00  
% 3.79/1.00  fof(f40,plain,(
% 3.79/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f41,plain,(
% 3.79/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f40])).
% 3.79/1.00  
% 3.79/1.00  fof(f59,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f41])).
% 3.79/1.00  
% 3.79/1.00  fof(f58,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f41])).
% 3.79/1.00  
% 3.79/1.00  fof(f60,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f41])).
% 3.79/1.00  
% 3.79/1.00  fof(f11,axiom,(
% 3.79/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f27,plain,(
% 3.79/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.79/1.00    inference(ennf_transformation,[],[f11])).
% 3.79/1.00  
% 3.79/1.00  fof(f28,plain,(
% 3.79/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.79/1.00    inference(flattening,[],[f27])).
% 3.79/1.00  
% 3.79/1.00  fof(f74,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f28])).
% 3.79/1.00  
% 3.79/1.00  fof(f10,axiom,(
% 3.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f19,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.79/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.79/1.00  
% 3.79/1.00  fof(f26,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.00    inference(ennf_transformation,[],[f19])).
% 3.79/1.00  
% 3.79/1.00  fof(f72,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f26])).
% 3.79/1.00  
% 3.79/1.00  fof(f12,axiom,(
% 3.79/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f29,plain,(
% 3.79/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.79/1.00    inference(ennf_transformation,[],[f12])).
% 3.79/1.00  
% 3.79/1.00  fof(f30,plain,(
% 3.79/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.79/1.00    inference(flattening,[],[f29])).
% 3.79/1.00  
% 3.79/1.00  fof(f46,plain,(
% 3.79/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.79/1.00    inference(nnf_transformation,[],[f30])).
% 3.79/1.00  
% 3.79/1.00  fof(f75,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f46])).
% 3.79/1.00  
% 3.79/1.00  fof(f9,axiom,(
% 3.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f25,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.00    inference(ennf_transformation,[],[f9])).
% 3.79/1.00  
% 3.79/1.00  fof(f71,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f25])).
% 3.79/1.00  
% 3.79/1.00  fof(f7,axiom,(
% 3.79/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f22,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(ennf_transformation,[],[f7])).
% 3.79/1.00  
% 3.79/1.00  fof(f68,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f22])).
% 3.79/1.00  
% 3.79/1.00  cnf(c_36,negated_conjecture,
% 3.79/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2107,plain,
% 3.79/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_11,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2121,plain,
% 3.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.79/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3539,plain,
% 3.79/1.00      ( r1_tarski(sK4,sK1) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2107,c_2121]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.79/1.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10,plain,
% 3.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_311,plain,
% 3.79/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.79/1.00      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_312,plain,
% 3.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_311]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_396,plain,
% 3.79/1.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.79/1.00      inference(bin_hyper_res,[status(thm)],[c_9,c_312]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2099,plain,
% 3.79/1.00      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.79/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5946,plain,
% 3.79/1.00      ( k9_subset_1(sK1,X0,sK4) = k3_xboole_0(X0,sK4) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_3539,c_2099]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_32,negated_conjecture,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 3.79/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2110,plain,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_21,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.79/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2118,plain,
% 3.79/1.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.79/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.79/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5084,plain,
% 3.79/1.00      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 3.79/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2110,c_2118]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_34,negated_conjecture,
% 3.79/1.00      ( v1_funct_1(sK5) ),
% 3.79/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2550,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.79/1.00      | ~ v1_funct_1(sK5)
% 3.79/1.00      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2706,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.79/1.00      | ~ v1_funct_1(sK5)
% 3.79/1.00      | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2550]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5538,plain,
% 3.79/1.00      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5084,c_34,c_32,c_2706]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_29,negated_conjecture,
% 3.79/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.79/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2113,plain,
% 3.79/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5083,plain,
% 3.79/1.00      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 3.79/1.00      | v1_funct_1(sK6) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2113,c_2118]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_31,negated_conjecture,
% 3.79/1.00      ( v1_funct_1(sK6) ),
% 3.79/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2545,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.79/1.00      | ~ v1_funct_1(sK6)
% 3.79/1.00      | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2700,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.79/1.00      | ~ v1_funct_1(sK6)
% 3.79/1.00      | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2545]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5356,plain,
% 3.79/1.00      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5083,c_31,c_29,c_2700]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_28,negated_conjecture,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.79/1.00      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.79/1.00      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5360,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.79/1.00      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.79/1.00      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_5356,c_28]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5542,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.79/1.00      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.79/1.00      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_5538,c_5360]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6515,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.79/1.00      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.79/1.00      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4)) ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_5946,c_5542]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_14,plain,
% 3.79/1.00      ( ~ r1_subset_1(X0,X1)
% 3.79/1.00      | r1_xboole_0(X0,X1)
% 3.79/1.00      | v1_xboole_0(X0)
% 3.79/1.00      | v1_xboole_0(X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_35,negated_conjecture,
% 3.79/1.00      ( r1_subset_1(sK3,sK4) ),
% 3.79/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_597,plain,
% 3.79/1.00      ( r1_xboole_0(X0,X1)
% 3.79/1.00      | v1_xboole_0(X0)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | sK4 != X1
% 3.79/1.00      | sK3 != X0 ),
% 3.79/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_35]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_598,plain,
% 3.79/1.00      ( r1_xboole_0(sK3,sK4) | v1_xboole_0(sK4) | v1_xboole_0(sK3) ),
% 3.79/1.00      inference(unflattening,[status(thm)],[c_597]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_39,negated_conjecture,
% 3.79/1.00      ( ~ v1_xboole_0(sK3) ),
% 3.79/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_37,negated_conjecture,
% 3.79/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.79/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_600,plain,
% 3.79/1.00      ( r1_xboole_0(sK3,sK4) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_598,c_39,c_37]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2098,plain,
% 3.79/1.00      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1,plain,
% 3.79/1.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2128,plain,
% 3.79/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3001,plain,
% 3.79/1.00      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2098,c_2128]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6516,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.79/1.00      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.79/1.00      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_6515,c_3001]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_41,negated_conjecture,
% 3.79/1.00      ( ~ v1_xboole_0(sK1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_38,negated_conjecture,
% 3.79/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_24,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_1(X3)
% 3.79/1.00      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.79/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_27,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_1(X3)
% 3.79/1.00      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_26,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_1(X3)
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_25,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_1(X3)
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_226,plain,
% 3.79/1.00      ( ~ v1_funct_1(X3)
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_24,c_27,c_26,c_25]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_227,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_1(X3)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_226]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2101,plain,
% 3.79/1.00      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.79/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.79/1.00      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.79/1.00      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.79/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.79/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.79/1.00      | v1_funct_1(X2) != iProver_top
% 3.79/1.00      | v1_funct_1(X5) != iProver_top
% 3.79/1.00      | v1_xboole_0(X3) = iProver_top
% 3.79/1.00      | v1_xboole_0(X1) = iProver_top
% 3.79/1.00      | v1_xboole_0(X4) = iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5361,plain,
% 3.79/1.00      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 3.79/1.00      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.79/1.00      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top
% 3.79/1.00      | v1_funct_1(sK6) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top
% 3.79/1.00      | v1_xboole_0(X2) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK2) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_5356,c_2101]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_40,negated_conjecture,
% 3.79/1.00      ( ~ v1_xboole_0(sK2) ),
% 3.79/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_43,plain,
% 3.79/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_46,plain,
% 3.79/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_52,plain,
% 3.79/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_30,negated_conjecture,
% 3.79/1.00      ( v1_funct_2(sK6,sK4,sK2) ),
% 3.79/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_53,plain,
% 3.79/1.00      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_54,plain,
% 3.79/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5721,plain,
% 3.79/1.00      ( v1_funct_1(X1) != iProver_top
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.79/1.00      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 3.79/1.00      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top
% 3.79/1.00      | v1_xboole_0(X2) = iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5361,c_43,c_46,c_52,c_53,c_54]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5722,plain,
% 3.79/1.00      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 3.79/1.00      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top
% 3.79/1.00      | v1_xboole_0(X2) = iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_5721]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5737,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.79/1.00      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.79/1.00      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.79/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | v1_funct_1(sK5) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_5538,c_5722]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_44,plain,
% 3.79/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_49,plain,
% 3.79/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_33,negated_conjecture,
% 3.79/1.00      ( v1_funct_2(sK5,sK3,sK2) ),
% 3.79/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_50,plain,
% 3.79/1.00      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_51,plain,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5861,plain,
% 3.79/1.00      ( v1_xboole_0(X0) = iProver_top
% 3.79/1.00      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.79/1.00      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5737,c_44,c_49,c_50,c_51]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5862,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.79/1.00      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_5861]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6524,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.79/1.00      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_5946,c_5862]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6530,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.79/1.00      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_6524,c_3001]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6531,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.79/1.00      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_6530,c_5946]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6532,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.79/1.00      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_6531,c_3001]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6698,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 3.79/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.79/1.00      | v1_xboole_0(sK1)
% 3.79/1.00      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.79/1.00      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 3.79/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6532]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_23,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_1(X3)
% 3.79/1.00      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_233,plain,
% 3.79/1.00      ( ~ v1_funct_1(X3)
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_23,c_27,c_26,c_25]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_234,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_2(X3,X4,X2)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_funct_1(X3)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | v1_xboole_0(X4)
% 3.79/1.00      | v1_xboole_0(X5)
% 3.79/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_233]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2100,plain,
% 3.79/1.00      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.79/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.79/1.00      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.79/1.00      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.79/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.79/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.79/1.00      | v1_funct_1(X2) != iProver_top
% 3.79/1.00      | v1_funct_1(X5) != iProver_top
% 3.79/1.00      | v1_xboole_0(X3) = iProver_top
% 3.79/1.00      | v1_xboole_0(X1) = iProver_top
% 3.79/1.00      | v1_xboole_0(X4) = iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5362,plain,
% 3.79/1.00      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 3.79/1.00      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.79/1.00      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top
% 3.79/1.00      | v1_funct_1(sK6) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top
% 3.79/1.00      | v1_xboole_0(X2) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK2) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_5356,c_2100]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7271,plain,
% 3.79/1.00      ( v1_funct_1(X1) != iProver_top
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.79/1.00      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 3.79/1.00      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top
% 3.79/1.00      | v1_xboole_0(X2) = iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5362,c_43,c_46,c_52,c_53,c_54]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7272,plain,
% 3.79/1.00      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 3.79/1.00      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 3.79/1.00      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top
% 3.79/1.00      | v1_xboole_0(X2) = iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_7271]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7287,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.79/1.00      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.79/1.00      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.79/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | v1_funct_1(sK5) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_5538,c_7272]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7404,plain,
% 3.79/1.00      ( v1_xboole_0(X0) = iProver_top
% 3.79/1.00      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.79/1.00      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_7287,c_44,c_49,c_50,c_51]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7405,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.79/1.00      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_7404]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7415,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.79/1.00      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_5946,c_7405]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7435,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.79/1.00      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_7415,c_3001]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7436,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.79/1.00      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_7435,c_5946]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7437,plain,
% 3.79/1.00      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.79/1.00      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
% 3.79/1.00      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_7436,c_3001]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7444,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 3.79/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.79/1.00      | v1_xboole_0(sK1)
% 3.79/1.00      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.79/1.00      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 3.79/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7437]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10201,plain,
% 3.79/1.00      ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_6516,c_41,c_38,c_36,c_6698,c_7444]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_8,plain,
% 3.79/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_0,plain,
% 3.79/1.00      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2129,plain,
% 3.79/1.00      ( k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3457,plain,
% 3.79/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_8,c_2129]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3,plain,
% 3.79/1.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2126,plain,
% 3.79/1.00      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.79/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4,plain,
% 3.79/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2125,plain,
% 3.79/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.79/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2127,plain,
% 3.79/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.79/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.79/1.00      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5063,plain,
% 3.79/1.00      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 3.79/1.00      | r1_xboole_0(X2,X0) != iProver_top
% 3.79/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2125,c_2127]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7734,plain,
% 3.79/1.00      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2126,c_5063]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7749,plain,
% 3.79/1.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_3457,c_7734]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_17,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | v1_partfun1(X0,X1)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | v1_xboole_0(X2) ),
% 3.79/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_16,plain,
% 3.79/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.79/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_20,plain,
% 3.79/1.00      ( ~ v1_partfun1(X0,X1)
% 3.79/1.00      | ~ v4_relat_1(X0,X1)
% 3.79/1.00      | ~ v1_relat_1(X0)
% 3.79/1.00      | k1_relat_1(X0) = X1 ),
% 3.79/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_534,plain,
% 3.79/1.00      ( ~ v1_partfun1(X0,X1)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_relat_1(X0)
% 3.79/1.00      | k1_relat_1(X0) = X1 ),
% 3.79/1.00      inference(resolution,[status(thm)],[c_16,c_20]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_15,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_538,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_partfun1(X0,X1)
% 3.79/1.00      | k1_relat_1(X0) = X1 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_534,c_20,c_16,c_15]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_539,plain,
% 3.79/1.00      ( ~ v1_partfun1(X0,X1)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | k1_relat_1(X0) = X1 ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_538]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_610,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | k1_relat_1(X0) = X1 ),
% 3.79/1.00      inference(resolution,[status(thm)],[c_17,c_539]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_614,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | k1_relat_1(X0) = X1 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_610,c_20,c_17,c_16,c_15]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_615,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | k1_relat_1(X0) = X1 ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_614]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2097,plain,
% 3.79/1.00      ( k1_relat_1(X0) = X1
% 3.79/1.00      | v1_funct_2(X0,X1,X2) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.79/1.00      | v1_funct_1(X0) != iProver_top
% 3.79/1.00      | v1_xboole_0(X2) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2856,plain,
% 3.79/1.00      ( k1_relat_1(sK6) = sK4
% 3.79/1.00      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 3.79/1.00      | v1_funct_1(sK6) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2113,c_2097]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2555,plain,
% 3.79/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 3.79/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.79/1.00      | ~ v1_funct_1(sK6)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | k1_relat_1(sK6) = X0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_615]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2715,plain,
% 3.79/1.00      ( ~ v1_funct_2(sK6,sK4,sK2)
% 3.79/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.79/1.00      | ~ v1_funct_1(sK6)
% 3.79/1.00      | v1_xboole_0(sK2)
% 3.79/1.00      | k1_relat_1(sK6) = sK4 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2555]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2995,plain,
% 3.79/1.00      ( k1_relat_1(sK6) = sK4 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_2856,c_40,c_31,c_30,c_29,c_2715]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_12,plain,
% 3.79/1.00      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 3.79/1.00      | ~ v1_relat_1(X1)
% 3.79/1.00      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2120,plain,
% 3.79/1.00      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.79/1.00      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 3.79/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4028,plain,
% 3.79/1.00      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 3.79/1.00      | r1_xboole_0(X0,sK4) != iProver_top
% 3.79/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2995,c_2120]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2494,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.79/1.00      | v1_relat_1(sK6) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2495,plain,
% 3.79/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.79/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2494]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4211,plain,
% 3.79/1.00      ( r1_xboole_0(X0,sK4) != iProver_top | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_4028,c_54,c_2495]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4212,plain,
% 3.79/1.00      ( k7_relat_1(sK6,X0) = k1_xboole_0 | r1_xboole_0(X0,sK4) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_4211]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7799,plain,
% 3.79/1.00      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_7749,c_4212]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2852,plain,
% 3.79/1.00      ( k1_relat_1(sK5) = sK3
% 3.79/1.00      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.79/1.00      | v1_funct_1(sK5) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2110,c_2097]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2560,plain,
% 3.79/1.00      ( ~ v1_funct_2(sK5,X0,X1)
% 3.79/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.79/1.00      | ~ v1_funct_1(sK5)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | k1_relat_1(sK5) = X0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_615]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2718,plain,
% 3.79/1.00      ( ~ v1_funct_2(sK5,sK3,sK2)
% 3.79/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.79/1.00      | ~ v1_funct_1(sK5)
% 3.79/1.00      | v1_xboole_0(sK2)
% 3.79/1.00      | k1_relat_1(sK5) = sK3 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2560]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2905,plain,
% 3.79/1.00      ( k1_relat_1(sK5) = sK3 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_2852,c_40,c_34,c_33,c_32,c_2718]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4029,plain,
% 3.79/1.00      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 3.79/1.00      | r1_xboole_0(X0,sK3) != iProver_top
% 3.79/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2905,c_2120]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2497,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.79/1.00      | v1_relat_1(sK5) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2498,plain,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.79/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2497]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4693,plain,
% 3.79/1.00      ( r1_xboole_0(X0,sK3) != iProver_top | k7_relat_1(sK5,X0) = k1_xboole_0 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_4029,c_51,c_2498]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4694,plain,
% 3.79/1.00      ( k7_relat_1(sK5,X0) = k1_xboole_0 | r1_xboole_0(X0,sK3) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_4693]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7800,plain,
% 3.79/1.00      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_7749,c_4694]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10203,plain,
% 3.79/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_10201,c_7799,c_7800]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10204,plain,
% 3.79/1.00      ( $false ),
% 3.79/1.00      inference(equality_resolution_simp,[status(thm)],[c_10203]) ).
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  ------                               Statistics
% 3.79/1.00  
% 3.79/1.00  ------ General
% 3.79/1.00  
% 3.79/1.00  abstr_ref_over_cycles:                  0
% 3.79/1.00  abstr_ref_under_cycles:                 0
% 3.79/1.00  gc_basic_clause_elim:                   0
% 3.79/1.00  forced_gc_time:                         0
% 3.79/1.00  parsing_time:                           0.011
% 3.79/1.00  unif_index_cands_time:                  0.
% 3.79/1.00  unif_index_add_time:                    0.
% 3.79/1.00  orderings_time:                         0.
% 3.79/1.00  out_proof_time:                         0.016
% 3.79/1.00  total_time:                             0.479
% 3.79/1.00  num_of_symbols:                         59
% 3.79/1.00  num_of_terms:                           15489
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing
% 3.79/1.00  
% 3.79/1.00  num_of_splits:                          0
% 3.79/1.00  num_of_split_atoms:                     0
% 3.79/1.00  num_of_reused_defs:                     0
% 3.79/1.00  num_eq_ax_congr_red:                    33
% 3.79/1.00  num_of_sem_filtered_clauses:            1
% 3.79/1.00  num_of_subtypes:                        0
% 3.79/1.00  monotx_restored_types:                  0
% 3.79/1.00  sat_num_of_epr_types:                   0
% 3.79/1.00  sat_num_of_non_cyclic_types:            0
% 3.79/1.00  sat_guarded_non_collapsed_types:        0
% 3.79/1.00  num_pure_diseq_elim:                    0
% 3.79/1.00  simp_replaced_by:                       0
% 3.79/1.00  res_preprocessed:                       176
% 3.79/1.00  prep_upred:                             0
% 3.79/1.00  prep_unflattend:                        42
% 3.79/1.00  smt_new_axioms:                         0
% 3.79/1.00  pred_elim_cands:                        8
% 3.79/1.00  pred_elim:                              3
% 3.79/1.00  pred_elim_cl:                           5
% 3.79/1.00  pred_elim_cycles:                       7
% 3.79/1.00  merged_defs:                            16
% 3.79/1.00  merged_defs_ncl:                        0
% 3.79/1.00  bin_hyper_res:                          17
% 3.79/1.00  prep_cycles:                            4
% 3.79/1.00  pred_elim_time:                         0.008
% 3.79/1.00  splitting_time:                         0.
% 3.79/1.00  sem_filter_time:                        0.
% 3.79/1.00  monotx_time:                            0.001
% 3.79/1.00  subtype_inf_time:                       0.
% 3.79/1.00  
% 3.79/1.00  ------ Problem properties
% 3.79/1.00  
% 3.79/1.00  clauses:                                35
% 3.79/1.00  conjectures:                            13
% 3.79/1.00  epr:                                    12
% 3.79/1.00  horn:                                   26
% 3.79/1.00  ground:                                 14
% 3.79/1.00  unary:                                  15
% 3.79/1.00  binary:                                 8
% 3.79/1.00  lits:                                   135
% 3.79/1.00  lits_eq:                                17
% 3.79/1.00  fd_pure:                                0
% 3.79/1.00  fd_pseudo:                              0
% 3.79/1.00  fd_cond:                                0
% 3.79/1.00  fd_pseudo_cond:                         2
% 3.79/1.00  ac_symbols:                             0
% 3.79/1.00  
% 3.79/1.00  ------ Propositional Solver
% 3.79/1.00  
% 3.79/1.00  prop_solver_calls:                      27
% 3.79/1.00  prop_fast_solver_calls:                 1952
% 3.79/1.00  smt_solver_calls:                       0
% 3.79/1.00  smt_fast_solver_calls:                  0
% 3.79/1.00  prop_num_of_clauses:                    3792
% 3.79/1.00  prop_preprocess_simplified:             9347
% 3.79/1.00  prop_fo_subsumed:                       89
% 3.79/1.00  prop_solver_time:                       0.
% 3.79/1.00  smt_solver_time:                        0.
% 3.79/1.00  smt_fast_solver_time:                   0.
% 3.79/1.00  prop_fast_solver_time:                  0.
% 3.79/1.00  prop_unsat_core_time:                   0.
% 3.79/1.00  
% 3.79/1.00  ------ QBF
% 3.79/1.00  
% 3.79/1.00  qbf_q_res:                              0
% 3.79/1.00  qbf_num_tautologies:                    0
% 3.79/1.00  qbf_prep_cycles:                        0
% 3.79/1.00  
% 3.79/1.00  ------ BMC1
% 3.79/1.00  
% 3.79/1.00  bmc1_current_bound:                     -1
% 3.79/1.00  bmc1_last_solved_bound:                 -1
% 3.79/1.00  bmc1_unsat_core_size:                   -1
% 3.79/1.00  bmc1_unsat_core_parents_size:           -1
% 3.79/1.00  bmc1_merge_next_fun:                    0
% 3.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.79/1.00  
% 3.79/1.00  ------ Instantiation
% 3.79/1.00  
% 3.79/1.00  inst_num_of_clauses:                    923
% 3.79/1.00  inst_num_in_passive:                    431
% 3.79/1.00  inst_num_in_active:                     472
% 3.79/1.00  inst_num_in_unprocessed:                23
% 3.79/1.00  inst_num_of_loops:                      490
% 3.79/1.00  inst_num_of_learning_restarts:          0
% 3.79/1.00  inst_num_moves_active_passive:          14
% 3.79/1.00  inst_lit_activity:                      0
% 3.79/1.00  inst_lit_activity_moves:                0
% 3.79/1.00  inst_num_tautologies:                   0
% 3.79/1.00  inst_num_prop_implied:                  0
% 3.79/1.00  inst_num_existing_simplified:           0
% 3.79/1.00  inst_num_eq_res_simplified:             0
% 3.79/1.00  inst_num_child_elim:                    0
% 3.79/1.00  inst_num_of_dismatching_blockings:      230
% 3.79/1.00  inst_num_of_non_proper_insts:           706
% 3.79/1.00  inst_num_of_duplicates:                 0
% 3.79/1.00  inst_inst_num_from_inst_to_res:         0
% 3.79/1.00  inst_dismatching_checking_time:         0.
% 3.79/1.00  
% 3.79/1.00  ------ Resolution
% 3.79/1.00  
% 3.79/1.00  res_num_of_clauses:                     0
% 3.79/1.00  res_num_in_passive:                     0
% 3.79/1.00  res_num_in_active:                      0
% 3.79/1.00  res_num_of_loops:                       180
% 3.79/1.00  res_forward_subset_subsumed:            35
% 3.79/1.00  res_backward_subset_subsumed:           6
% 3.79/1.00  res_forward_subsumed:                   0
% 3.79/1.00  res_backward_subsumed:                  0
% 3.79/1.00  res_forward_subsumption_resolution:     1
% 3.79/1.00  res_backward_subsumption_resolution:    0
% 3.79/1.00  res_clause_to_clause_subsumption:       425
% 3.79/1.00  res_orphan_elimination:                 0
% 3.79/1.00  res_tautology_del:                      61
% 3.79/1.00  res_num_eq_res_simplified:              0
% 3.79/1.00  res_num_sel_changes:                    0
% 3.79/1.00  res_moves_from_active_to_pass:          0
% 3.79/1.00  
% 3.79/1.00  ------ Superposition
% 3.79/1.00  
% 3.79/1.00  sup_time_total:                         0.
% 3.79/1.00  sup_time_generating:                    0.
% 3.79/1.00  sup_time_sim_full:                      0.
% 3.79/1.00  sup_time_sim_immed:                     0.
% 3.79/1.00  
% 3.79/1.00  sup_num_of_clauses:                     155
% 3.79/1.00  sup_num_in_active:                      93
% 3.79/1.00  sup_num_in_passive:                     62
% 3.79/1.00  sup_num_of_loops:                       96
% 3.79/1.00  sup_fw_superposition:                   104
% 3.79/1.00  sup_bw_superposition:                   62
% 3.79/1.00  sup_immediate_simplified:               75
% 3.79/1.00  sup_given_eliminated:                   0
% 3.79/1.00  comparisons_done:                       0
% 3.79/1.00  comparisons_avoided:                    0
% 3.79/1.00  
% 3.79/1.00  ------ Simplifications
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  sim_fw_subset_subsumed:                 0
% 3.79/1.00  sim_bw_subset_subsumed:                 0
% 3.79/1.00  sim_fw_subsumed:                        6
% 3.79/1.00  sim_bw_subsumed:                        2
% 3.79/1.00  sim_fw_subsumption_res:                 0
% 3.79/1.00  sim_bw_subsumption_res:                 0
% 3.79/1.00  sim_tautology_del:                      2
% 3.79/1.00  sim_eq_tautology_del:                   1
% 3.79/1.00  sim_eq_res_simp:                        0
% 3.79/1.00  sim_fw_demodulated:                     46
% 3.79/1.00  sim_bw_demodulated:                     3
% 3.79/1.00  sim_light_normalised:                   34
% 3.79/1.00  sim_joinable_taut:                      0
% 3.79/1.00  sim_joinable_simp:                      0
% 3.79/1.00  sim_ac_normalised:                      0
% 3.79/1.00  sim_smt_subsumption:                    0
% 3.79/1.00  
%------------------------------------------------------------------------------
