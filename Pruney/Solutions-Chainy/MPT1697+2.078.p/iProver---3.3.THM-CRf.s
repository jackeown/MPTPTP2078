%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:40 EST 2020

% Result     : Theorem 11.12s
% Output     : CNFRefutation 11.12s
% Verified   : 
% Statistics : Number of formulae       :  250 (1891 expanded)
%              Number of clauses        :  156 ( 507 expanded)
%              Number of leaves         :   25 ( 718 expanded)
%              Depth                    :   25
%              Number of atoms          : 1289 (23175 expanded)
%              Number of equality atoms :  498 (5552 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f39,f55,f54,f53,f52,f51,f50])).

fof(f91,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f95,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

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
    inference(flattening,[],[f48])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f77])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1135,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2016,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1135])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_13])).

cnf(c_1124,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_relat_1(X0_55)
    | k7_relat_1(X0_55,X1_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_486])).

cnf(c_2027,plain,
    ( k7_relat_1(X0_55,X1_55) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1124])).

cnf(c_6616,plain,
    ( k7_relat_1(sK6,sK4) = sK6
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_2027])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1146,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2006,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1146])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1147,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ v1_relat_1(X1_55)
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2005,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
    | v1_relat_1(X1_55) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_3602,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK3)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_2005])).

cnf(c_3915,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_3602])).

cnf(c_6669,plain,
    ( k7_relat_1(sK6,sK4) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6616,c_3915])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1153,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1999,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1151,plain,
    ( r1_xboole_0(X0_55,X1_55)
    | r2_hidden(sK1(X0_55,X1_55),X1_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2001,plain,
    ( r1_xboole_0(X0_55,X1_55) = iProver_top
    | r2_hidden(sK1(X0_55,X1_55),X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1156,plain,
    ( ~ r2_hidden(X0_58,X0_55)
    | ~ v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1996,plain,
    ( r2_hidden(X0_58,X0_55) != iProver_top
    | v1_xboole_0(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_3164,plain,
    ( r1_xboole_0(X0_55,X1_55) = iProver_top
    | v1_xboole_0(X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_2001,c_1996])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1154,plain,
    ( ~ r1_xboole_0(X0_55,X1_55)
    | k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1998,plain,
    ( k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0
    | r1_xboole_0(X0_55,X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_4201,plain,
    ( k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0
    | v1_xboole_0(X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_1998])).

cnf(c_4242,plain,
    ( k1_setfam_1(k2_tarski(X0_55,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1999,c_4201])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1155,plain,
    ( r1_xboole_0(X0_55,X1_55)
    | k1_setfam_1(k2_tarski(X0_55,X1_55)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1997,plain,
    ( k1_setfam_1(k2_tarski(X0_55,X1_55)) != k1_xboole_0
    | r1_xboole_0(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_4632,plain,
    ( r1_xboole_0(X0_55,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4242,c_1997])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1145,plain,
    ( ~ r1_xboole_0(X0_55,X1_55)
    | ~ v1_relat_1(X2_55)
    | k7_relat_1(k7_relat_1(X2_55,X0_55),X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2007,plain,
    ( k7_relat_1(k7_relat_1(X0_55,X1_55),X2_55) = k1_xboole_0
    | r1_xboole_0(X1_55,X2_55) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_4639,plain,
    ( k7_relat_1(k7_relat_1(X0_55,X1_55),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_4632,c_2007])).

cnf(c_6708,plain,
    ( k7_relat_1(k7_relat_1(sK6,X0_55),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3915,c_4639])).

cnf(c_13113,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6669,c_6708])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1138,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2013,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_6615,plain,
    ( k7_relat_1(sK7,sK5) = sK7
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_2027])).

cnf(c_3601,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK3)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_2005])).

cnf(c_3912,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_3601])).

cnf(c_6666,plain,
    ( k7_relat_1(sK7,sK5) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6615,c_3912])).

cnf(c_6707,plain,
    ( k7_relat_1(k7_relat_1(sK7,X0_55),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3912,c_4639])).

cnf(c_11253,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6666,c_6707])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1132,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2019,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_1140,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55))
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2012,plain,
    ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
    | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X3_55) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55)) = iProver_top
    | v1_xboole_0(X5_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_1142,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2010,plain,
    ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
    | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X3_55) != iProver_top
    | v1_xboole_0(X5_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1142])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1144,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2008,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_4155,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
    | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
    | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X4_55) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55)) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_2010,c_2008])).

cnf(c_8315,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
    | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
    | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X4_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_4155])).

cnf(c_8375,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK5),sK3,k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55)
    | v1_funct_2(X2_55,X1_55,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_8315])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_42,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_48,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_49,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1148,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ v1_xboole_0(X1_55)
    | v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2221,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0_55))
    | ~ v1_xboole_0(X0_55)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_2222,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_xboole_0(X0_55) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2221])).

cnf(c_8388,plain,
    ( v1_xboole_0(X1_55) = iProver_top
    | v1_funct_2(X2_55,X1_55,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X0_55,X1_55,sK5),sK3,k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55)
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8375,c_39,c_42,c_48,c_49,c_2222])).

cnf(c_8389,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK5),sK3,k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55)
    | v1_funct_2(X2_55,X1_55,sK3) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_8388])).

cnf(c_8395,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),X1_55)
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_8389])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_45,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_46,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8595,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),X1_55)
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8395,c_40,c_45,c_46])).

cnf(c_8601,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_55) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_55)
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2019,c_8595])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8606,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_55) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8601,c_41])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | k9_subset_1(X1_55,X2_55,X0_55) = k1_setfam_1(k2_tarski(X2_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2003,plain,
    ( k9_subset_1(X0_55,X1_55,X2_55) = k1_setfam_1(k2_tarski(X1_55,X2_55))
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_3157,plain,
    ( k9_subset_1(sK2,X0_55,sK5) = k1_setfam_1(k2_tarski(X0_55,sK5)) ),
    inference(superposition,[status(thm)],[c_2019,c_2003])).

cnf(c_24,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1139,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3609,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(demodulation,[status(thm)],[c_3157,c_1139])).

cnf(c_15,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_505,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_506,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_35,c_33])).

cnf(c_1123,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_508])).

cnf(c_2028,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_3080,plain,
    ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2028,c_1998])).

cnf(c_3610,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3609,c_3080])).

cnf(c_3802,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_55) = k7_relat_1(sK7,X0_55)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_2008])).

cnf(c_3933,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_55) = k7_relat_1(sK7,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3802,c_48])).

cnf(c_3803,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_55) = k7_relat_1(sK6,X0_55)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_2008])).

cnf(c_3937,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_55) = k7_relat_1(sK6,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3803,c_45])).

cnf(c_3977,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3610,c_3933,c_3937])).

cnf(c_8609,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8606,c_3977])).

cnf(c_8610,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8609,c_8606])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f102])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_202,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_23,c_22,c_21])).

cnf(c_203,plain,
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
    inference(renaming,[status(thm)],[c_202])).

cnf(c_1126,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_2025,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
    | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_4511,plain,
    ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3933,c_2025])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5936,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
    | k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4511,c_39,c_42,c_48,c_49,c_50])).

cnf(c_5937,plain,
    ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_5936])).

cnf(c_5943,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3937,c_5937])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2185,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0_55))
    | ~ v1_xboole_0(X0_55)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_2186,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_xboole_0(X0_55) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2185])).

cnf(c_6024,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5943,c_40,c_45,c_46,c_47,c_2186])).

cnf(c_6025,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6024])).

cnf(c_6030,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3157,c_6025])).

cnf(c_6031,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6030,c_3080])).

cnf(c_6032,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6031,c_3157])).

cnf(c_6033,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6032,c_3080])).

cnf(c_6034,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6033])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f101])).

cnf(c_209,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_23,c_22,c_21])).

cnf(c_210,plain,
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
    inference(renaming,[status(thm)],[c_209])).

cnf(c_1125,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_210])).

cnf(c_2026,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
    | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_6220,plain,
    ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3933,c_2026])).

cnf(c_6886,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
    | k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6220,c_39,c_42,c_48,c_49,c_50])).

cnf(c_6887,plain,
    ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_6886])).

cnf(c_6893,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3937,c_6887])).

cnf(c_6926,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6893,c_40,c_45,c_46,c_47,c_2186])).

cnf(c_6927,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6926])).

cnf(c_6932,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3157,c_6927])).

cnf(c_6933,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6932,c_3080])).

cnf(c_6934,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6933,c_3157])).

cnf(c_6935,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6934,c_3080])).

cnf(c_6936,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6935])).

cnf(c_9743,plain,
    ( k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8610,c_34,c_32,c_3977,c_6034,c_6936])).

cnf(c_11278,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11253,c_9743])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13113,c_11278])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.12/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.12/2.01  
% 11.12/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.12/2.01  
% 11.12/2.01  ------  iProver source info
% 11.12/2.01  
% 11.12/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.12/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.12/2.01  git: non_committed_changes: false
% 11.12/2.01  git: last_make_outside_of_git: false
% 11.12/2.01  
% 11.12/2.01  ------ 
% 11.12/2.01  
% 11.12/2.01  ------ Input Options
% 11.12/2.01  
% 11.12/2.01  --out_options                           all
% 11.12/2.01  --tptp_safe_out                         true
% 11.12/2.01  --problem_path                          ""
% 11.12/2.01  --include_path                          ""
% 11.12/2.01  --clausifier                            res/vclausify_rel
% 11.12/2.01  --clausifier_options                    ""
% 11.12/2.01  --stdin                                 false
% 11.12/2.01  --stats_out                             all
% 11.12/2.01  
% 11.12/2.01  ------ General Options
% 11.12/2.01  
% 11.12/2.01  --fof                                   false
% 11.12/2.01  --time_out_real                         305.
% 11.12/2.01  --time_out_virtual                      -1.
% 11.12/2.01  --symbol_type_check                     false
% 11.12/2.01  --clausify_out                          false
% 11.12/2.01  --sig_cnt_out                           false
% 11.12/2.01  --trig_cnt_out                          false
% 11.12/2.01  --trig_cnt_out_tolerance                1.
% 11.12/2.01  --trig_cnt_out_sk_spl                   false
% 11.12/2.01  --abstr_cl_out                          false
% 11.12/2.01  
% 11.12/2.01  ------ Global Options
% 11.12/2.01  
% 11.12/2.01  --schedule                              default
% 11.12/2.01  --add_important_lit                     false
% 11.12/2.01  --prop_solver_per_cl                    1000
% 11.12/2.01  --min_unsat_core                        false
% 11.12/2.01  --soft_assumptions                      false
% 11.12/2.01  --soft_lemma_size                       3
% 11.12/2.01  --prop_impl_unit_size                   0
% 11.12/2.01  --prop_impl_unit                        []
% 11.12/2.01  --share_sel_clauses                     true
% 11.12/2.01  --reset_solvers                         false
% 11.12/2.01  --bc_imp_inh                            [conj_cone]
% 11.12/2.01  --conj_cone_tolerance                   3.
% 11.12/2.01  --extra_neg_conj                        none
% 11.12/2.01  --large_theory_mode                     true
% 11.12/2.01  --prolific_symb_bound                   200
% 11.12/2.01  --lt_threshold                          2000
% 11.12/2.01  --clause_weak_htbl                      true
% 11.12/2.01  --gc_record_bc_elim                     false
% 11.12/2.01  
% 11.12/2.01  ------ Preprocessing Options
% 11.12/2.01  
% 11.12/2.01  --preprocessing_flag                    true
% 11.12/2.01  --time_out_prep_mult                    0.1
% 11.12/2.01  --splitting_mode                        input
% 11.12/2.01  --splitting_grd                         true
% 11.12/2.01  --splitting_cvd                         false
% 11.12/2.01  --splitting_cvd_svl                     false
% 11.12/2.01  --splitting_nvd                         32
% 11.12/2.01  --sub_typing                            true
% 11.12/2.01  --prep_gs_sim                           true
% 11.12/2.01  --prep_unflatten                        true
% 11.12/2.01  --prep_res_sim                          true
% 11.12/2.01  --prep_upred                            true
% 11.12/2.01  --prep_sem_filter                       exhaustive
% 11.12/2.01  --prep_sem_filter_out                   false
% 11.12/2.01  --pred_elim                             true
% 11.12/2.01  --res_sim_input                         true
% 11.12/2.01  --eq_ax_congr_red                       true
% 11.12/2.01  --pure_diseq_elim                       true
% 11.12/2.01  --brand_transform                       false
% 11.12/2.01  --non_eq_to_eq                          false
% 11.12/2.01  --prep_def_merge                        true
% 11.12/2.01  --prep_def_merge_prop_impl              false
% 11.12/2.01  --prep_def_merge_mbd                    true
% 11.12/2.01  --prep_def_merge_tr_red                 false
% 11.12/2.01  --prep_def_merge_tr_cl                  false
% 11.12/2.01  --smt_preprocessing                     true
% 11.12/2.01  --smt_ac_axioms                         fast
% 11.12/2.01  --preprocessed_out                      false
% 11.12/2.01  --preprocessed_stats                    false
% 11.12/2.01  
% 11.12/2.01  ------ Abstraction refinement Options
% 11.12/2.01  
% 11.12/2.01  --abstr_ref                             []
% 11.12/2.01  --abstr_ref_prep                        false
% 11.12/2.01  --abstr_ref_until_sat                   false
% 11.12/2.01  --abstr_ref_sig_restrict                funpre
% 11.12/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.12/2.01  --abstr_ref_under                       []
% 11.12/2.01  
% 11.12/2.01  ------ SAT Options
% 11.12/2.01  
% 11.12/2.01  --sat_mode                              false
% 11.12/2.01  --sat_fm_restart_options                ""
% 11.12/2.01  --sat_gr_def                            false
% 11.12/2.01  --sat_epr_types                         true
% 11.12/2.01  --sat_non_cyclic_types                  false
% 11.12/2.01  --sat_finite_models                     false
% 11.12/2.01  --sat_fm_lemmas                         false
% 11.12/2.01  --sat_fm_prep                           false
% 11.12/2.01  --sat_fm_uc_incr                        true
% 11.12/2.01  --sat_out_model                         small
% 11.12/2.01  --sat_out_clauses                       false
% 11.12/2.01  
% 11.12/2.01  ------ QBF Options
% 11.12/2.01  
% 11.12/2.01  --qbf_mode                              false
% 11.12/2.01  --qbf_elim_univ                         false
% 11.12/2.01  --qbf_dom_inst                          none
% 11.12/2.01  --qbf_dom_pre_inst                      false
% 11.12/2.01  --qbf_sk_in                             false
% 11.12/2.01  --qbf_pred_elim                         true
% 11.12/2.01  --qbf_split                             512
% 11.12/2.01  
% 11.12/2.01  ------ BMC1 Options
% 11.12/2.01  
% 11.12/2.01  --bmc1_incremental                      false
% 11.12/2.01  --bmc1_axioms                           reachable_all
% 11.12/2.01  --bmc1_min_bound                        0
% 11.12/2.01  --bmc1_max_bound                        -1
% 11.12/2.01  --bmc1_max_bound_default                -1
% 11.12/2.01  --bmc1_symbol_reachability              true
% 11.12/2.01  --bmc1_property_lemmas                  false
% 11.12/2.01  --bmc1_k_induction                      false
% 11.12/2.01  --bmc1_non_equiv_states                 false
% 11.12/2.01  --bmc1_deadlock                         false
% 11.12/2.01  --bmc1_ucm                              false
% 11.12/2.01  --bmc1_add_unsat_core                   none
% 11.12/2.01  --bmc1_unsat_core_children              false
% 11.12/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.12/2.01  --bmc1_out_stat                         full
% 11.12/2.01  --bmc1_ground_init                      false
% 11.12/2.01  --bmc1_pre_inst_next_state              false
% 11.12/2.01  --bmc1_pre_inst_state                   false
% 11.12/2.01  --bmc1_pre_inst_reach_state             false
% 11.12/2.01  --bmc1_out_unsat_core                   false
% 11.12/2.01  --bmc1_aig_witness_out                  false
% 11.12/2.01  --bmc1_verbose                          false
% 11.12/2.01  --bmc1_dump_clauses_tptp                false
% 11.12/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.12/2.01  --bmc1_dump_file                        -
% 11.12/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.12/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.12/2.01  --bmc1_ucm_extend_mode                  1
% 11.12/2.01  --bmc1_ucm_init_mode                    2
% 11.12/2.01  --bmc1_ucm_cone_mode                    none
% 11.12/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.12/2.01  --bmc1_ucm_relax_model                  4
% 11.12/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.12/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.12/2.01  --bmc1_ucm_layered_model                none
% 11.12/2.01  --bmc1_ucm_max_lemma_size               10
% 11.12/2.01  
% 11.12/2.01  ------ AIG Options
% 11.12/2.01  
% 11.12/2.01  --aig_mode                              false
% 11.12/2.01  
% 11.12/2.01  ------ Instantiation Options
% 11.12/2.01  
% 11.12/2.01  --instantiation_flag                    true
% 11.12/2.01  --inst_sos_flag                         true
% 11.12/2.01  --inst_sos_phase                        true
% 11.12/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.12/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.12/2.01  --inst_lit_sel_side                     num_symb
% 11.12/2.01  --inst_solver_per_active                1400
% 11.12/2.01  --inst_solver_calls_frac                1.
% 11.12/2.01  --inst_passive_queue_type               priority_queues
% 11.12/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.12/2.01  --inst_passive_queues_freq              [25;2]
% 11.12/2.01  --inst_dismatching                      true
% 11.12/2.01  --inst_eager_unprocessed_to_passive     true
% 11.12/2.01  --inst_prop_sim_given                   true
% 11.12/2.01  --inst_prop_sim_new                     false
% 11.12/2.01  --inst_subs_new                         false
% 11.12/2.01  --inst_eq_res_simp                      false
% 11.12/2.01  --inst_subs_given                       false
% 11.12/2.01  --inst_orphan_elimination               true
% 11.12/2.01  --inst_learning_loop_flag               true
% 11.12/2.01  --inst_learning_start                   3000
% 11.12/2.01  --inst_learning_factor                  2
% 11.12/2.01  --inst_start_prop_sim_after_learn       3
% 11.12/2.01  --inst_sel_renew                        solver
% 11.12/2.01  --inst_lit_activity_flag                true
% 11.12/2.01  --inst_restr_to_given                   false
% 11.12/2.01  --inst_activity_threshold               500
% 11.12/2.01  --inst_out_proof                        true
% 11.12/2.01  
% 11.12/2.01  ------ Resolution Options
% 11.12/2.01  
% 11.12/2.01  --resolution_flag                       true
% 11.12/2.01  --res_lit_sel                           adaptive
% 11.12/2.01  --res_lit_sel_side                      none
% 11.12/2.01  --res_ordering                          kbo
% 11.12/2.01  --res_to_prop_solver                    active
% 11.12/2.01  --res_prop_simpl_new                    false
% 11.12/2.01  --res_prop_simpl_given                  true
% 11.12/2.01  --res_passive_queue_type                priority_queues
% 11.12/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.12/2.01  --res_passive_queues_freq               [15;5]
% 11.12/2.01  --res_forward_subs                      full
% 11.12/2.01  --res_backward_subs                     full
% 11.12/2.01  --res_forward_subs_resolution           true
% 11.12/2.01  --res_backward_subs_resolution          true
% 11.12/2.01  --res_orphan_elimination                true
% 11.12/2.01  --res_time_limit                        2.
% 11.12/2.01  --res_out_proof                         true
% 11.12/2.01  
% 11.12/2.01  ------ Superposition Options
% 11.12/2.01  
% 11.12/2.01  --superposition_flag                    true
% 11.12/2.01  --sup_passive_queue_type                priority_queues
% 11.12/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.12/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.12/2.01  --demod_completeness_check              fast
% 11.12/2.01  --demod_use_ground                      true
% 11.12/2.01  --sup_to_prop_solver                    passive
% 11.12/2.01  --sup_prop_simpl_new                    true
% 11.12/2.01  --sup_prop_simpl_given                  true
% 11.12/2.01  --sup_fun_splitting                     true
% 11.12/2.01  --sup_smt_interval                      50000
% 11.12/2.01  
% 11.12/2.01  ------ Superposition Simplification Setup
% 11.12/2.01  
% 11.12/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.12/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.12/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.12/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.12/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.12/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.12/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.12/2.01  --sup_immed_triv                        [TrivRules]
% 11.12/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.12/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.12/2.01  --sup_immed_bw_main                     []
% 11.12/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.12/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.12/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.12/2.01  --sup_input_bw                          []
% 11.12/2.01  
% 11.12/2.01  ------ Combination Options
% 11.12/2.01  
% 11.12/2.01  --comb_res_mult                         3
% 11.12/2.01  --comb_sup_mult                         2
% 11.12/2.01  --comb_inst_mult                        10
% 11.12/2.01  
% 11.12/2.01  ------ Debug Options
% 11.12/2.01  
% 11.12/2.01  --dbg_backtrace                         false
% 11.12/2.01  --dbg_dump_prop_clauses                 false
% 11.12/2.01  --dbg_dump_prop_clauses_file            -
% 11.12/2.01  --dbg_out_stat                          false
% 11.12/2.01  ------ Parsing...
% 11.12/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.12/2.01  
% 11.12/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.12/2.01  
% 11.12/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.12/2.01  
% 11.12/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.12/2.01  ------ Proving...
% 11.12/2.01  ------ Problem Properties 
% 11.12/2.01  
% 11.12/2.01  
% 11.12/2.01  clauses                                 35
% 11.12/2.01  conjectures                             13
% 11.12/2.01  EPR                                     12
% 11.12/2.01  Horn                                    26
% 11.12/2.01  unary                                   15
% 11.12/2.01  binary                                  7
% 11.12/2.01  lits                                    134
% 11.12/2.01  lits eq                                 15
% 11.12/2.01  fd_pure                                 0
% 11.12/2.01  fd_pseudo                               0
% 11.12/2.01  fd_cond                                 0
% 11.12/2.01  fd_pseudo_cond                          0
% 11.12/2.01  AC symbols                              0
% 11.12/2.01  
% 11.12/2.01  ------ Schedule dynamic 5 is on 
% 11.12/2.01  
% 11.12/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.12/2.01  
% 11.12/2.01  
% 11.12/2.01  ------ 
% 11.12/2.01  Current options:
% 11.12/2.01  ------ 
% 11.12/2.01  
% 11.12/2.01  ------ Input Options
% 11.12/2.01  
% 11.12/2.01  --out_options                           all
% 11.12/2.01  --tptp_safe_out                         true
% 11.12/2.01  --problem_path                          ""
% 11.12/2.01  --include_path                          ""
% 11.12/2.01  --clausifier                            res/vclausify_rel
% 11.12/2.01  --clausifier_options                    ""
% 11.12/2.01  --stdin                                 false
% 11.12/2.01  --stats_out                             all
% 11.12/2.01  
% 11.12/2.01  ------ General Options
% 11.12/2.01  
% 11.12/2.01  --fof                                   false
% 11.12/2.01  --time_out_real                         305.
% 11.12/2.01  --time_out_virtual                      -1.
% 11.12/2.01  --symbol_type_check                     false
% 11.12/2.01  --clausify_out                          false
% 11.12/2.01  --sig_cnt_out                           false
% 11.12/2.01  --trig_cnt_out                          false
% 11.12/2.01  --trig_cnt_out_tolerance                1.
% 11.12/2.01  --trig_cnt_out_sk_spl                   false
% 11.12/2.01  --abstr_cl_out                          false
% 11.12/2.01  
% 11.12/2.01  ------ Global Options
% 11.12/2.01  
% 11.12/2.01  --schedule                              default
% 11.12/2.01  --add_important_lit                     false
% 11.12/2.01  --prop_solver_per_cl                    1000
% 11.12/2.01  --min_unsat_core                        false
% 11.12/2.01  --soft_assumptions                      false
% 11.12/2.01  --soft_lemma_size                       3
% 11.12/2.01  --prop_impl_unit_size                   0
% 11.12/2.01  --prop_impl_unit                        []
% 11.12/2.01  --share_sel_clauses                     true
% 11.12/2.01  --reset_solvers                         false
% 11.12/2.01  --bc_imp_inh                            [conj_cone]
% 11.12/2.01  --conj_cone_tolerance                   3.
% 11.12/2.01  --extra_neg_conj                        none
% 11.12/2.01  --large_theory_mode                     true
% 11.12/2.01  --prolific_symb_bound                   200
% 11.12/2.01  --lt_threshold                          2000
% 11.12/2.01  --clause_weak_htbl                      true
% 11.12/2.01  --gc_record_bc_elim                     false
% 11.12/2.01  
% 11.12/2.01  ------ Preprocessing Options
% 11.12/2.01  
% 11.12/2.01  --preprocessing_flag                    true
% 11.12/2.01  --time_out_prep_mult                    0.1
% 11.12/2.01  --splitting_mode                        input
% 11.12/2.01  --splitting_grd                         true
% 11.12/2.01  --splitting_cvd                         false
% 11.12/2.01  --splitting_cvd_svl                     false
% 11.12/2.01  --splitting_nvd                         32
% 11.12/2.01  --sub_typing                            true
% 11.12/2.01  --prep_gs_sim                           true
% 11.12/2.01  --prep_unflatten                        true
% 11.12/2.01  --prep_res_sim                          true
% 11.12/2.01  --prep_upred                            true
% 11.12/2.01  --prep_sem_filter                       exhaustive
% 11.12/2.01  --prep_sem_filter_out                   false
% 11.12/2.01  --pred_elim                             true
% 11.12/2.01  --res_sim_input                         true
% 11.12/2.01  --eq_ax_congr_red                       true
% 11.12/2.01  --pure_diseq_elim                       true
% 11.12/2.01  --brand_transform                       false
% 11.12/2.01  --non_eq_to_eq                          false
% 11.12/2.01  --prep_def_merge                        true
% 11.12/2.01  --prep_def_merge_prop_impl              false
% 11.12/2.01  --prep_def_merge_mbd                    true
% 11.12/2.01  --prep_def_merge_tr_red                 false
% 11.12/2.01  --prep_def_merge_tr_cl                  false
% 11.12/2.01  --smt_preprocessing                     true
% 11.12/2.01  --smt_ac_axioms                         fast
% 11.12/2.01  --preprocessed_out                      false
% 11.12/2.01  --preprocessed_stats                    false
% 11.12/2.01  
% 11.12/2.01  ------ Abstraction refinement Options
% 11.12/2.01  
% 11.12/2.01  --abstr_ref                             []
% 11.12/2.01  --abstr_ref_prep                        false
% 11.12/2.01  --abstr_ref_until_sat                   false
% 11.12/2.01  --abstr_ref_sig_restrict                funpre
% 11.12/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.12/2.01  --abstr_ref_under                       []
% 11.12/2.01  
% 11.12/2.01  ------ SAT Options
% 11.12/2.01  
% 11.12/2.01  --sat_mode                              false
% 11.12/2.01  --sat_fm_restart_options                ""
% 11.12/2.01  --sat_gr_def                            false
% 11.12/2.01  --sat_epr_types                         true
% 11.12/2.01  --sat_non_cyclic_types                  false
% 11.12/2.01  --sat_finite_models                     false
% 11.12/2.01  --sat_fm_lemmas                         false
% 11.12/2.01  --sat_fm_prep                           false
% 11.12/2.01  --sat_fm_uc_incr                        true
% 11.12/2.01  --sat_out_model                         small
% 11.12/2.01  --sat_out_clauses                       false
% 11.12/2.01  
% 11.12/2.01  ------ QBF Options
% 11.12/2.01  
% 11.12/2.01  --qbf_mode                              false
% 11.12/2.01  --qbf_elim_univ                         false
% 11.12/2.01  --qbf_dom_inst                          none
% 11.12/2.01  --qbf_dom_pre_inst                      false
% 11.12/2.01  --qbf_sk_in                             false
% 11.12/2.01  --qbf_pred_elim                         true
% 11.12/2.01  --qbf_split                             512
% 11.12/2.01  
% 11.12/2.01  ------ BMC1 Options
% 11.12/2.01  
% 11.12/2.01  --bmc1_incremental                      false
% 11.12/2.01  --bmc1_axioms                           reachable_all
% 11.12/2.01  --bmc1_min_bound                        0
% 11.12/2.01  --bmc1_max_bound                        -1
% 11.12/2.01  --bmc1_max_bound_default                -1
% 11.12/2.01  --bmc1_symbol_reachability              true
% 11.12/2.01  --bmc1_property_lemmas                  false
% 11.12/2.01  --bmc1_k_induction                      false
% 11.12/2.01  --bmc1_non_equiv_states                 false
% 11.12/2.01  --bmc1_deadlock                         false
% 11.12/2.01  --bmc1_ucm                              false
% 11.12/2.01  --bmc1_add_unsat_core                   none
% 11.12/2.01  --bmc1_unsat_core_children              false
% 11.12/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.12/2.01  --bmc1_out_stat                         full
% 11.12/2.01  --bmc1_ground_init                      false
% 11.12/2.01  --bmc1_pre_inst_next_state              false
% 11.12/2.01  --bmc1_pre_inst_state                   false
% 11.12/2.01  --bmc1_pre_inst_reach_state             false
% 11.12/2.01  --bmc1_out_unsat_core                   false
% 11.12/2.01  --bmc1_aig_witness_out                  false
% 11.12/2.01  --bmc1_verbose                          false
% 11.12/2.01  --bmc1_dump_clauses_tptp                false
% 11.12/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.12/2.01  --bmc1_dump_file                        -
% 11.12/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.12/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.12/2.01  --bmc1_ucm_extend_mode                  1
% 11.12/2.01  --bmc1_ucm_init_mode                    2
% 11.12/2.01  --bmc1_ucm_cone_mode                    none
% 11.12/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.12/2.01  --bmc1_ucm_relax_model                  4
% 11.12/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.12/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.12/2.01  --bmc1_ucm_layered_model                none
% 11.12/2.01  --bmc1_ucm_max_lemma_size               10
% 11.12/2.01  
% 11.12/2.01  ------ AIG Options
% 11.12/2.01  
% 11.12/2.01  --aig_mode                              false
% 11.12/2.01  
% 11.12/2.01  ------ Instantiation Options
% 11.12/2.01  
% 11.12/2.01  --instantiation_flag                    true
% 11.12/2.01  --inst_sos_flag                         true
% 11.12/2.01  --inst_sos_phase                        true
% 11.12/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.12/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.12/2.01  --inst_lit_sel_side                     none
% 11.12/2.01  --inst_solver_per_active                1400
% 11.12/2.01  --inst_solver_calls_frac                1.
% 11.12/2.01  --inst_passive_queue_type               priority_queues
% 11.12/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.12/2.01  --inst_passive_queues_freq              [25;2]
% 11.12/2.01  --inst_dismatching                      true
% 11.12/2.01  --inst_eager_unprocessed_to_passive     true
% 11.12/2.01  --inst_prop_sim_given                   true
% 11.12/2.01  --inst_prop_sim_new                     false
% 11.12/2.01  --inst_subs_new                         false
% 11.12/2.01  --inst_eq_res_simp                      false
% 11.12/2.01  --inst_subs_given                       false
% 11.12/2.01  --inst_orphan_elimination               true
% 11.12/2.01  --inst_learning_loop_flag               true
% 11.12/2.01  --inst_learning_start                   3000
% 11.12/2.01  --inst_learning_factor                  2
% 11.12/2.01  --inst_start_prop_sim_after_learn       3
% 11.12/2.01  --inst_sel_renew                        solver
% 11.12/2.01  --inst_lit_activity_flag                true
% 11.12/2.01  --inst_restr_to_given                   false
% 11.12/2.01  --inst_activity_threshold               500
% 11.12/2.01  --inst_out_proof                        true
% 11.12/2.01  
% 11.12/2.01  ------ Resolution Options
% 11.12/2.01  
% 11.12/2.01  --resolution_flag                       false
% 11.12/2.01  --res_lit_sel                           adaptive
% 11.12/2.01  --res_lit_sel_side                      none
% 11.12/2.01  --res_ordering                          kbo
% 11.12/2.01  --res_to_prop_solver                    active
% 11.12/2.01  --res_prop_simpl_new                    false
% 11.12/2.01  --res_prop_simpl_given                  true
% 11.12/2.01  --res_passive_queue_type                priority_queues
% 11.12/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.12/2.01  --res_passive_queues_freq               [15;5]
% 11.12/2.01  --res_forward_subs                      full
% 11.12/2.01  --res_backward_subs                     full
% 11.12/2.01  --res_forward_subs_resolution           true
% 11.12/2.01  --res_backward_subs_resolution          true
% 11.12/2.01  --res_orphan_elimination                true
% 11.12/2.01  --res_time_limit                        2.
% 11.12/2.01  --res_out_proof                         true
% 11.12/2.01  
% 11.12/2.01  ------ Superposition Options
% 11.12/2.01  
% 11.12/2.01  --superposition_flag                    true
% 11.12/2.01  --sup_passive_queue_type                priority_queues
% 11.12/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.12/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.12/2.01  --demod_completeness_check              fast
% 11.12/2.01  --demod_use_ground                      true
% 11.12/2.01  --sup_to_prop_solver                    passive
% 11.12/2.01  --sup_prop_simpl_new                    true
% 11.12/2.01  --sup_prop_simpl_given                  true
% 11.12/2.01  --sup_fun_splitting                     true
% 11.12/2.01  --sup_smt_interval                      50000
% 11.12/2.01  
% 11.12/2.01  ------ Superposition Simplification Setup
% 11.12/2.01  
% 11.12/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.12/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.12/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.12/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.12/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.12/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.12/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.12/2.01  --sup_immed_triv                        [TrivRules]
% 11.12/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.12/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.12/2.01  --sup_immed_bw_main                     []
% 11.12/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.12/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.12/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.12/2.01  --sup_input_bw                          []
% 11.12/2.01  
% 11.12/2.01  ------ Combination Options
% 11.12/2.01  
% 11.12/2.01  --comb_res_mult                         3
% 11.12/2.01  --comb_sup_mult                         2
% 11.12/2.01  --comb_inst_mult                        10
% 11.12/2.01  
% 11.12/2.01  ------ Debug Options
% 11.12/2.01  
% 11.12/2.01  --dbg_backtrace                         false
% 11.12/2.01  --dbg_dump_prop_clauses                 false
% 11.12/2.01  --dbg_dump_prop_clauses_file            -
% 11.12/2.01  --dbg_out_stat                          false
% 11.12/2.01  
% 11.12/2.01  
% 11.12/2.01  
% 11.12/2.01  
% 11.12/2.01  ------ Proving...
% 11.12/2.01  
% 11.12/2.01  
% 11.12/2.01  % SZS status Theorem for theBenchmark.p
% 11.12/2.01  
% 11.12/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.12/2.01  
% 11.12/2.01  fof(f17,conjecture,(
% 11.12/2.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f18,negated_conjecture,(
% 11.12/2.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.12/2.01    inference(negated_conjecture,[],[f17])).
% 11.12/2.01  
% 11.12/2.01  fof(f38,plain,(
% 11.12/2.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.12/2.01    inference(ennf_transformation,[],[f18])).
% 11.12/2.01  
% 11.12/2.01  fof(f39,plain,(
% 11.12/2.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.12/2.01    inference(flattening,[],[f38])).
% 11.12/2.01  
% 11.12/2.01  fof(f55,plain,(
% 11.12/2.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 11.12/2.01    introduced(choice_axiom,[])).
% 11.12/2.01  
% 11.12/2.01  fof(f54,plain,(
% 11.12/2.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 11.12/2.01    introduced(choice_axiom,[])).
% 11.12/2.01  
% 11.12/2.01  fof(f53,plain,(
% 11.12/2.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 11.12/2.01    introduced(choice_axiom,[])).
% 11.12/2.01  
% 11.12/2.01  fof(f52,plain,(
% 11.12/2.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 11.12/2.01    introduced(choice_axiom,[])).
% 11.12/2.01  
% 11.12/2.01  fof(f51,plain,(
% 11.12/2.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 11.12/2.01    introduced(choice_axiom,[])).
% 11.12/2.01  
% 11.12/2.01  fof(f50,plain,(
% 11.12/2.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 11.12/2.01    introduced(choice_axiom,[])).
% 11.12/2.01  
% 11.12/2.01  fof(f56,plain,(
% 11.12/2.01    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 11.12/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f39,f55,f54,f53,f52,f51,f50])).
% 11.12/2.01  
% 11.12/2.01  fof(f91,plain,(
% 11.12/2.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f13,axiom,(
% 11.12/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f20,plain,(
% 11.12/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.12/2.01    inference(pure_predicate_removal,[],[f13])).
% 11.12/2.01  
% 11.12/2.01  fof(f31,plain,(
% 11.12/2.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.12/2.01    inference(ennf_transformation,[],[f20])).
% 11.12/2.01  
% 11.12/2.01  fof(f74,plain,(
% 11.12/2.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.12/2.01    inference(cnf_transformation,[],[f31])).
% 11.12/2.01  
% 11.12/2.01  fof(f11,axiom,(
% 11.12/2.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f27,plain,(
% 11.12/2.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.12/2.01    inference(ennf_transformation,[],[f11])).
% 11.12/2.01  
% 11.12/2.01  fof(f28,plain,(
% 11.12/2.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.12/2.01    inference(flattening,[],[f27])).
% 11.12/2.01  
% 11.12/2.01  fof(f71,plain,(
% 11.12/2.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f28])).
% 11.12/2.01  
% 11.12/2.01  fof(f9,axiom,(
% 11.12/2.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f69,plain,(
% 11.12/2.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.12/2.01    inference(cnf_transformation,[],[f9])).
% 11.12/2.01  
% 11.12/2.01  fof(f8,axiom,(
% 11.12/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f24,plain,(
% 11.12/2.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.12/2.01    inference(ennf_transformation,[],[f8])).
% 11.12/2.01  
% 11.12/2.01  fof(f68,plain,(
% 11.12/2.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f24])).
% 11.12/2.01  
% 11.12/2.01  fof(f3,axiom,(
% 11.12/2.01    v1_xboole_0(k1_xboole_0)),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f61,plain,(
% 11.12/2.01    v1_xboole_0(k1_xboole_0)),
% 11.12/2.01    inference(cnf_transformation,[],[f3])).
% 11.12/2.01  
% 11.12/2.01  fof(f4,axiom,(
% 11.12/2.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f19,plain,(
% 11.12/2.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.12/2.01    inference(rectify,[],[f4])).
% 11.12/2.01  
% 11.12/2.01  fof(f21,plain,(
% 11.12/2.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.12/2.01    inference(ennf_transformation,[],[f19])).
% 11.12/2.01  
% 11.12/2.01  fof(f45,plain,(
% 11.12/2.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.12/2.01    introduced(choice_axiom,[])).
% 11.12/2.01  
% 11.12/2.01  fof(f46,plain,(
% 11.12/2.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.12/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f45])).
% 11.12/2.01  
% 11.12/2.01  fof(f63,plain,(
% 11.12/2.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f46])).
% 11.12/2.01  
% 11.12/2.01  fof(f1,axiom,(
% 11.12/2.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f40,plain,(
% 11.12/2.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.12/2.01    inference(nnf_transformation,[],[f1])).
% 11.12/2.01  
% 11.12/2.01  fof(f41,plain,(
% 11.12/2.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.12/2.01    inference(rectify,[],[f40])).
% 11.12/2.01  
% 11.12/2.01  fof(f42,plain,(
% 11.12/2.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.12/2.01    introduced(choice_axiom,[])).
% 11.12/2.01  
% 11.12/2.01  fof(f43,plain,(
% 11.12/2.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.12/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 11.12/2.01  
% 11.12/2.01  fof(f57,plain,(
% 11.12/2.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f43])).
% 11.12/2.01  
% 11.12/2.01  fof(f2,axiom,(
% 11.12/2.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f44,plain,(
% 11.12/2.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.12/2.01    inference(nnf_transformation,[],[f2])).
% 11.12/2.01  
% 11.12/2.01  fof(f59,plain,(
% 11.12/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f44])).
% 11.12/2.01  
% 11.12/2.01  fof(f7,axiom,(
% 11.12/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f67,plain,(
% 11.12/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.12/2.01    inference(cnf_transformation,[],[f7])).
% 11.12/2.01  
% 11.12/2.01  fof(f97,plain,(
% 11.12/2.01    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.12/2.01    inference(definition_unfolding,[],[f59,f67])).
% 11.12/2.01  
% 11.12/2.01  fof(f60,plain,(
% 11.12/2.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.12/2.01    inference(cnf_transformation,[],[f44])).
% 11.12/2.01  
% 11.12/2.01  fof(f96,plain,(
% 11.12/2.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.12/2.01    inference(definition_unfolding,[],[f60,f67])).
% 11.12/2.01  
% 11.12/2.01  fof(f10,axiom,(
% 11.12/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f25,plain,(
% 11.12/2.01    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 11.12/2.01    inference(ennf_transformation,[],[f10])).
% 11.12/2.01  
% 11.12/2.01  fof(f26,plain,(
% 11.12/2.01    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 11.12/2.01    inference(flattening,[],[f25])).
% 11.12/2.01  
% 11.12/2.01  fof(f70,plain,(
% 11.12/2.01    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f26])).
% 11.12/2.01  
% 11.12/2.01  fof(f94,plain,(
% 11.12/2.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f87,plain,(
% 11.12/2.01    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f16,axiom,(
% 11.12/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f36,plain,(
% 11.12/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.12/2.01    inference(ennf_transformation,[],[f16])).
% 11.12/2.01  
% 11.12/2.01  fof(f37,plain,(
% 11.12/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.12/2.01    inference(flattening,[],[f36])).
% 11.12/2.01  
% 11.12/2.01  fof(f79,plain,(
% 11.12/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f37])).
% 11.12/2.01  
% 11.12/2.01  fof(f81,plain,(
% 11.12/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f37])).
% 11.12/2.01  
% 11.12/2.01  fof(f14,axiom,(
% 11.12/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f32,plain,(
% 11.12/2.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.12/2.01    inference(ennf_transformation,[],[f14])).
% 11.12/2.01  
% 11.12/2.01  fof(f33,plain,(
% 11.12/2.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.12/2.01    inference(flattening,[],[f32])).
% 11.12/2.01  
% 11.12/2.01  fof(f75,plain,(
% 11.12/2.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f33])).
% 11.12/2.01  
% 11.12/2.01  fof(f83,plain,(
% 11.12/2.01    ~v1_xboole_0(sK3)),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f86,plain,(
% 11.12/2.01    ~v1_xboole_0(sK5)),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f92,plain,(
% 11.12/2.01    v1_funct_1(sK7)),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f93,plain,(
% 11.12/2.01    v1_funct_2(sK7,sK5,sK3)),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f6,axiom,(
% 11.12/2.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f23,plain,(
% 11.12/2.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 11.12/2.01    inference(ennf_transformation,[],[f6])).
% 11.12/2.01  
% 11.12/2.01  fof(f66,plain,(
% 11.12/2.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f23])).
% 11.12/2.01  
% 11.12/2.01  fof(f84,plain,(
% 11.12/2.01    ~v1_xboole_0(sK4)),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f89,plain,(
% 11.12/2.01    v1_funct_1(sK6)),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f90,plain,(
% 11.12/2.01    v1_funct_2(sK6,sK4,sK3)),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f85,plain,(
% 11.12/2.01    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f5,axiom,(
% 11.12/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f22,plain,(
% 11.12/2.01    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.12/2.01    inference(ennf_transformation,[],[f5])).
% 11.12/2.01  
% 11.12/2.01  fof(f65,plain,(
% 11.12/2.01    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.12/2.01    inference(cnf_transformation,[],[f22])).
% 11.12/2.01  
% 11.12/2.01  fof(f98,plain,(
% 11.12/2.01    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.12/2.01    inference(definition_unfolding,[],[f65,f67])).
% 11.12/2.01  
% 11.12/2.01  fof(f95,plain,(
% 11.12/2.01    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f12,axiom,(
% 11.12/2.01    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f29,plain,(
% 11.12/2.01    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.12/2.01    inference(ennf_transformation,[],[f12])).
% 11.12/2.01  
% 11.12/2.01  fof(f30,plain,(
% 11.12/2.01    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.12/2.01    inference(flattening,[],[f29])).
% 11.12/2.01  
% 11.12/2.01  fof(f47,plain,(
% 11.12/2.01    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.12/2.01    inference(nnf_transformation,[],[f30])).
% 11.12/2.01  
% 11.12/2.01  fof(f72,plain,(
% 11.12/2.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f47])).
% 11.12/2.01  
% 11.12/2.01  fof(f88,plain,(
% 11.12/2.01    r1_subset_1(sK4,sK5)),
% 11.12/2.01    inference(cnf_transformation,[],[f56])).
% 11.12/2.01  
% 11.12/2.01  fof(f15,axiom,(
% 11.12/2.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 11.12/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/2.01  
% 11.12/2.01  fof(f34,plain,(
% 11.12/2.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.12/2.01    inference(ennf_transformation,[],[f15])).
% 11.12/2.01  
% 11.12/2.01  fof(f35,plain,(
% 11.12/2.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.12/2.01    inference(flattening,[],[f34])).
% 11.12/2.01  
% 11.12/2.01  fof(f48,plain,(
% 11.12/2.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.12/2.01    inference(nnf_transformation,[],[f35])).
% 11.12/2.01  
% 11.12/2.01  fof(f49,plain,(
% 11.12/2.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.12/2.01    inference(flattening,[],[f48])).
% 11.12/2.01  
% 11.12/2.01  fof(f76,plain,(
% 11.12/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f49])).
% 11.12/2.01  
% 11.12/2.01  fof(f102,plain,(
% 11.12/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.12/2.01    inference(equality_resolution,[],[f76])).
% 11.12/2.01  
% 11.12/2.01  fof(f80,plain,(
% 11.12/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f37])).
% 11.12/2.01  
% 11.12/2.01  fof(f77,plain,(
% 11.12/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.12/2.01    inference(cnf_transformation,[],[f49])).
% 11.12/2.01  
% 11.12/2.01  fof(f101,plain,(
% 11.12/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.12/2.01    inference(equality_resolution,[],[f77])).
% 11.12/2.01  
% 11.12/2.01  cnf(c_28,negated_conjecture,
% 11.12/2.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 11.12/2.01      inference(cnf_transformation,[],[f91]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1135,negated_conjecture,
% 11.12/2.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_28]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_2016,plain,
% 11.12/2.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1135]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_16,plain,
% 11.12/2.01      ( v4_relat_1(X0,X1)
% 11.12/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.12/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_13,plain,
% 11.12/2.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.12/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_486,plain,
% 11.12/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.01      | ~ v1_relat_1(X0)
% 11.12/2.01      | k7_relat_1(X0,X1) = X0 ),
% 11.12/2.01      inference(resolution,[status(thm)],[c_16,c_13]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1124,plain,
% 11.12/2.01      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 11.12/2.01      | ~ v1_relat_1(X0_55)
% 11.12/2.01      | k7_relat_1(X0_55,X1_55) = X0_55 ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_486]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_2027,plain,
% 11.12/2.01      ( k7_relat_1(X0_55,X1_55) = X0_55
% 11.12/2.01      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 11.12/2.01      | v1_relat_1(X0_55) != iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1124]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_6616,plain,
% 11.12/2.01      ( k7_relat_1(sK6,sK4) = sK6 | v1_relat_1(sK6) != iProver_top ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_2016,c_2027]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_11,plain,
% 11.12/2.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.12/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1146,plain,
% 11.12/2.01      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_11]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_2006,plain,
% 11.12/2.01      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1146]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_10,plain,
% 11.12/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.12/2.01      | ~ v1_relat_1(X1)
% 11.12/2.01      | v1_relat_1(X0) ),
% 11.12/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1147,plain,
% 11.12/2.01      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 11.12/2.01      | ~ v1_relat_1(X1_55)
% 11.12/2.01      | v1_relat_1(X0_55) ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_10]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_2005,plain,
% 11.12/2.01      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
% 11.12/2.01      | v1_relat_1(X1_55) != iProver_top
% 11.12/2.01      | v1_relat_1(X0_55) = iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1147]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_3602,plain,
% 11.12/2.01      ( v1_relat_1(k2_zfmisc_1(sK4,sK3)) != iProver_top
% 11.12/2.01      | v1_relat_1(sK6) = iProver_top ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_2016,c_2005]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_3915,plain,
% 11.12/2.01      ( v1_relat_1(sK6) = iProver_top ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_2006,c_3602]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_6669,plain,
% 11.12/2.01      ( k7_relat_1(sK6,sK4) = sK6 ),
% 11.12/2.01      inference(global_propositional_subsumption,
% 11.12/2.01                [status(thm)],
% 11.12/2.01                [c_6616,c_3915]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_4,plain,
% 11.12/2.01      ( v1_xboole_0(k1_xboole_0) ),
% 11.12/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1153,plain,
% 11.12/2.01      ( v1_xboole_0(k1_xboole_0) ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_4]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1999,plain,
% 11.12/2.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_6,plain,
% 11.12/2.01      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 11.12/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1151,plain,
% 11.12/2.01      ( r1_xboole_0(X0_55,X1_55) | r2_hidden(sK1(X0_55,X1_55),X1_55) ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_6]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_2001,plain,
% 11.12/2.01      ( r1_xboole_0(X0_55,X1_55) = iProver_top
% 11.12/2.01      | r2_hidden(sK1(X0_55,X1_55),X1_55) = iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1,plain,
% 11.12/2.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.12/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1156,plain,
% 11.12/2.01      ( ~ r2_hidden(X0_58,X0_55) | ~ v1_xboole_0(X0_55) ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_1]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1996,plain,
% 11.12/2.01      ( r2_hidden(X0_58,X0_55) != iProver_top
% 11.12/2.01      | v1_xboole_0(X0_55) != iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_3164,plain,
% 11.12/2.01      ( r1_xboole_0(X0_55,X1_55) = iProver_top
% 11.12/2.01      | v1_xboole_0(X1_55) != iProver_top ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_2001,c_1996]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_3,plain,
% 11.12/2.01      ( ~ r1_xboole_0(X0,X1)
% 11.12/2.01      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 11.12/2.01      inference(cnf_transformation,[],[f97]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1154,plain,
% 11.12/2.01      ( ~ r1_xboole_0(X0_55,X1_55)
% 11.12/2.01      | k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0 ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_3]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1998,plain,
% 11.12/2.01      ( k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0
% 11.12/2.01      | r1_xboole_0(X0_55,X1_55) != iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_4201,plain,
% 11.12/2.01      ( k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0
% 11.12/2.01      | v1_xboole_0(X1_55) != iProver_top ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_3164,c_1998]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_4242,plain,
% 11.12/2.01      ( k1_setfam_1(k2_tarski(X0_55,k1_xboole_0)) = k1_xboole_0 ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_1999,c_4201]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_2,plain,
% 11.12/2.01      ( r1_xboole_0(X0,X1)
% 11.12/2.01      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 11.12/2.01      inference(cnf_transformation,[],[f96]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1155,plain,
% 11.12/2.01      ( r1_xboole_0(X0_55,X1_55)
% 11.12/2.01      | k1_setfam_1(k2_tarski(X0_55,X1_55)) != k1_xboole_0 ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_2]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1997,plain,
% 11.12/2.01      ( k1_setfam_1(k2_tarski(X0_55,X1_55)) != k1_xboole_0
% 11.12/2.01      | r1_xboole_0(X0_55,X1_55) = iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_4632,plain,
% 11.12/2.01      ( r1_xboole_0(X0_55,k1_xboole_0) = iProver_top ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_4242,c_1997]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_12,plain,
% 11.12/2.01      ( ~ r1_xboole_0(X0,X1)
% 11.12/2.01      | ~ v1_relat_1(X2)
% 11.12/2.01      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 11.12/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1145,plain,
% 11.12/2.01      ( ~ r1_xboole_0(X0_55,X1_55)
% 11.12/2.01      | ~ v1_relat_1(X2_55)
% 11.12/2.01      | k7_relat_1(k7_relat_1(X2_55,X0_55),X1_55) = k1_xboole_0 ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_12]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_2007,plain,
% 11.12/2.01      ( k7_relat_1(k7_relat_1(X0_55,X1_55),X2_55) = k1_xboole_0
% 11.12/2.01      | r1_xboole_0(X1_55,X2_55) != iProver_top
% 11.12/2.01      | v1_relat_1(X0_55) != iProver_top ),
% 11.12/2.01      inference(predicate_to_equality,[status(thm)],[c_1145]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_4639,plain,
% 11.12/2.01      ( k7_relat_1(k7_relat_1(X0_55,X1_55),k1_xboole_0) = k1_xboole_0
% 11.12/2.01      | v1_relat_1(X0_55) != iProver_top ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_4632,c_2007]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_6708,plain,
% 11.12/2.01      ( k7_relat_1(k7_relat_1(sK6,X0_55),k1_xboole_0) = k1_xboole_0 ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_3915,c_4639]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_13113,plain,
% 11.12/2.01      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 11.12/2.01      inference(superposition,[status(thm)],[c_6669,c_6708]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_25,negated_conjecture,
% 11.12/2.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 11.12/2.01      inference(cnf_transformation,[],[f94]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_1138,negated_conjecture,
% 11.12/2.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 11.12/2.01      inference(subtyping,[status(esa)],[c_25]) ).
% 11.12/2.01  
% 11.12/2.01  cnf(c_2013,plain,
% 11.12/2.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6615,plain,
% 11.12/2.02      ( k7_relat_1(sK7,sK5) = sK7 | v1_relat_1(sK7) != iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2013,c_2027]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3601,plain,
% 11.12/2.02      ( v1_relat_1(k2_zfmisc_1(sK5,sK3)) != iProver_top
% 11.12/2.02      | v1_relat_1(sK7) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2013,c_2005]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3912,plain,
% 11.12/2.02      ( v1_relat_1(sK7) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2006,c_3601]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6666,plain,
% 11.12/2.02      ( k7_relat_1(sK7,sK5) = sK7 ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_6615,c_3912]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6707,plain,
% 11.12/2.02      ( k7_relat_1(k7_relat_1(sK7,X0_55),k1_xboole_0) = k1_xboole_0 ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_3912,c_4639]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_11253,plain,
% 11.12/2.02      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_6666,c_6707]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_32,negated_conjecture,
% 11.12/2.02      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 11.12/2.02      inference(cnf_transformation,[],[f87]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1132,negated_conjecture,
% 11.12/2.02      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_32]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2019,plain,
% 11.12/2.02      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_23,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_1(X3)
% 11.12/2.02      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X1) ),
% 11.12/2.02      inference(cnf_transformation,[],[f79]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1140,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 11.12/2.02      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 11.12/2.02      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 11.12/2.02      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 11.12/2.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 11.12/2.02      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 11.12/2.02      | ~ v1_funct_1(X0_55)
% 11.12/2.02      | ~ v1_funct_1(X3_55)
% 11.12/2.02      | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55))
% 11.12/2.02      | v1_xboole_0(X1_55)
% 11.12/2.02      | v1_xboole_0(X2_55)
% 11.12/2.02      | v1_xboole_0(X4_55)
% 11.12/2.02      | v1_xboole_0(X5_55) ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_23]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2012,plain,
% 11.12/2.02      ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 11.12/2.02      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 11.12/2.02      | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 11.12/2.02      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 11.12/2.02      | v1_funct_1(X0_55) != iProver_top
% 11.12/2.02      | v1_funct_1(X3_55) != iProver_top
% 11.12/2.02      | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55)) = iProver_top
% 11.12/2.02      | v1_xboole_0(X5_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X4_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X1_55) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1140]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_21,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_1(X3)
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X1) ),
% 11.12/2.02      inference(cnf_transformation,[],[f81]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1142,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 11.12/2.02      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 11.12/2.02      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 11.12/2.02      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 11.12/2.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 11.12/2.02      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 11.12/2.02      | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55)))
% 11.12/2.02      | ~ v1_funct_1(X0_55)
% 11.12/2.02      | ~ v1_funct_1(X3_55)
% 11.12/2.02      | v1_xboole_0(X1_55)
% 11.12/2.02      | v1_xboole_0(X2_55)
% 11.12/2.02      | v1_xboole_0(X4_55)
% 11.12/2.02      | v1_xboole_0(X5_55) ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_21]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2010,plain,
% 11.12/2.02      ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 11.12/2.02      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 11.12/2.02      | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 11.12/2.02      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 11.12/2.02      | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55))) = iProver_top
% 11.12/2.02      | v1_funct_1(X0_55) != iProver_top
% 11.12/2.02      | v1_funct_1(X3_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(X5_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X4_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X1_55) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1142]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_17,plain,
% 11.12/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.12/2.02      inference(cnf_transformation,[],[f75]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1144,plain,
% 11.12/2.02      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 11.12/2.02      | ~ v1_funct_1(X0_55)
% 11.12/2.02      | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_17]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2008,plain,
% 11.12/2.02      ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 11.12/2.02      | v1_funct_1(X2_55) != iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1144]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_4155,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
% 11.12/2.02      | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
% 11.12/2.02      | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
% 11.12/2.02      | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
% 11.12/2.02      | v1_funct_1(X5_55) != iProver_top
% 11.12/2.02      | v1_funct_1(X4_55) != iProver_top
% 11.12/2.02      | v1_funct_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55)) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X1_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X3_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2010,c_2008]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8315,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
% 11.12/2.02      | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
% 11.12/2.02      | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
% 11.12/2.02      | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
% 11.12/2.02      | v1_funct_1(X5_55) != iProver_top
% 11.12/2.02      | v1_funct_1(X4_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X1_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X3_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2012,c_4155]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8375,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK5),sK3,k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55)
% 11.12/2.02      | v1_funct_2(X2_55,X1_55,sK3) != iProver_top
% 11.12/2.02      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(X2_55) != iProver_top
% 11.12/2.02      | v1_funct_1(sK7) != iProver_top
% 11.12/2.02      | v1_xboole_0(X1_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(sK3) = iProver_top
% 11.12/2.02      | v1_xboole_0(sK5) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2013,c_8315]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_36,negated_conjecture,
% 11.12/2.02      ( ~ v1_xboole_0(sK3) ),
% 11.12/2.02      inference(cnf_transformation,[],[f83]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_39,plain,
% 11.12/2.02      ( v1_xboole_0(sK3) != iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_33,negated_conjecture,
% 11.12/2.02      ( ~ v1_xboole_0(sK5) ),
% 11.12/2.02      inference(cnf_transformation,[],[f86]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_42,plain,
% 11.12/2.02      ( v1_xboole_0(sK5) != iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_27,negated_conjecture,
% 11.12/2.02      ( v1_funct_1(sK7) ),
% 11.12/2.02      inference(cnf_transformation,[],[f92]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_48,plain,
% 11.12/2.02      ( v1_funct_1(sK7) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_26,negated_conjecture,
% 11.12/2.02      ( v1_funct_2(sK7,sK5,sK3) ),
% 11.12/2.02      inference(cnf_transformation,[],[f93]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_49,plain,
% 11.12/2.02      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_9,plain,
% 11.12/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.12/2.02      | ~ v1_xboole_0(X1)
% 11.12/2.02      | v1_xboole_0(X0) ),
% 11.12/2.02      inference(cnf_transformation,[],[f66]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1148,plain,
% 11.12/2.02      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 11.12/2.02      | ~ v1_xboole_0(X1_55)
% 11.12/2.02      | v1_xboole_0(X0_55) ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_9]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2221,plain,
% 11.12/2.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0_55))
% 11.12/2.02      | ~ v1_xboole_0(X0_55)
% 11.12/2.02      | v1_xboole_0(sK5) ),
% 11.12/2.02      inference(instantiation,[status(thm)],[c_1148]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2222,plain,
% 11.12/2.02      ( m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(sK5) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_2221]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8388,plain,
% 11.12/2.02      ( v1_xboole_0(X1_55) = iProver_top
% 11.12/2.02      | v1_funct_2(X2_55,X1_55,sK3) != iProver_top
% 11.12/2.02      | k2_partfun1(k4_subset_1(X0_55,X1_55,sK5),sK3,k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55)
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(X2_55) != iProver_top ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_8375,c_39,c_42,c_48,c_49,c_2222]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8389,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK5),sK3,k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,X1_55,sK5,X2_55,sK7),X3_55)
% 11.12/2.02      | v1_funct_2(X2_55,X1_55,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(X2_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(X1_55) = iProver_top ),
% 11.12/2.02      inference(renaming,[status(thm)],[c_8388]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8395,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),X1_55)
% 11.12/2.02      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(sK6) != iProver_top
% 11.12/2.02      | v1_xboole_0(sK4) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2016,c_8389]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_35,negated_conjecture,
% 11.12/2.02      ( ~ v1_xboole_0(sK4) ),
% 11.12/2.02      inference(cnf_transformation,[],[f84]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_40,plain,
% 11.12/2.02      ( v1_xboole_0(sK4) != iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_30,negated_conjecture,
% 11.12/2.02      ( v1_funct_1(sK6) ),
% 11.12/2.02      inference(cnf_transformation,[],[f89]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_45,plain,
% 11.12/2.02      ( v1_funct_1(sK6) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_29,negated_conjecture,
% 11.12/2.02      ( v1_funct_2(sK6,sK4,sK3) ),
% 11.12/2.02      inference(cnf_transformation,[],[f90]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_46,plain,
% 11.12/2.02      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8595,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),X1_55)
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_8395,c_40,c_45,c_46]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8601,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_55) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_55)
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2019,c_8595]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_34,negated_conjecture,
% 11.12/2.02      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 11.12/2.02      inference(cnf_transformation,[],[f85]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_41,plain,
% 11.12/2.02      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8606,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_55) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_55) ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_8601,c_41]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8,plain,
% 11.12/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.12/2.02      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 11.12/2.02      inference(cnf_transformation,[],[f98]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1149,plain,
% 11.12/2.02      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 11.12/2.02      | k9_subset_1(X1_55,X2_55,X0_55) = k1_setfam_1(k2_tarski(X2_55,X0_55)) ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_8]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2003,plain,
% 11.12/2.02      ( k9_subset_1(X0_55,X1_55,X2_55) = k1_setfam_1(k2_tarski(X1_55,X2_55))
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3157,plain,
% 11.12/2.02      ( k9_subset_1(sK2,X0_55,sK5) = k1_setfam_1(k2_tarski(X0_55,sK5)) ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2019,c_2003]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_24,negated_conjecture,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 11.12/2.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 11.12/2.02      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 11.12/2.02      inference(cnf_transformation,[],[f95]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1139,negated_conjecture,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 11.12/2.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 11.12/2.02      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_24]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3609,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 11.12/2.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 11.12/2.02      | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 11.12/2.02      inference(demodulation,[status(thm)],[c_3157,c_1139]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_15,plain,
% 11.12/2.02      ( ~ r1_subset_1(X0,X1)
% 11.12/2.02      | r1_xboole_0(X0,X1)
% 11.12/2.02      | v1_xboole_0(X0)
% 11.12/2.02      | v1_xboole_0(X1) ),
% 11.12/2.02      inference(cnf_transformation,[],[f72]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_31,negated_conjecture,
% 11.12/2.02      ( r1_subset_1(sK4,sK5) ),
% 11.12/2.02      inference(cnf_transformation,[],[f88]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_505,plain,
% 11.12/2.02      ( r1_xboole_0(X0,X1)
% 11.12/2.02      | v1_xboole_0(X0)
% 11.12/2.02      | v1_xboole_0(X1)
% 11.12/2.02      | sK5 != X1
% 11.12/2.02      | sK4 != X0 ),
% 11.12/2.02      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_506,plain,
% 11.12/2.02      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 11.12/2.02      inference(unflattening,[status(thm)],[c_505]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_508,plain,
% 11.12/2.02      ( r1_xboole_0(sK4,sK5) ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_506,c_35,c_33]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1123,plain,
% 11.12/2.02      ( r1_xboole_0(sK4,sK5) ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_508]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2028,plain,
% 11.12/2.02      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3080,plain,
% 11.12/2.02      ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2028,c_1998]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3610,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 11.12/2.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 11.12/2.02      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
% 11.12/2.02      inference(light_normalisation,[status(thm)],[c_3609,c_3080]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3802,plain,
% 11.12/2.02      ( k2_partfun1(sK5,sK3,sK7,X0_55) = k7_relat_1(sK7,X0_55)
% 11.12/2.02      | v1_funct_1(sK7) != iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2013,c_2008]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3933,plain,
% 11.12/2.02      ( k2_partfun1(sK5,sK3,sK7,X0_55) = k7_relat_1(sK7,X0_55) ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_3802,c_48]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3803,plain,
% 11.12/2.02      ( k2_partfun1(sK4,sK3,sK6,X0_55) = k7_relat_1(sK6,X0_55)
% 11.12/2.02      | v1_funct_1(sK6) != iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_2016,c_2008]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3937,plain,
% 11.12/2.02      ( k2_partfun1(sK4,sK3,sK6,X0_55) = k7_relat_1(sK6,X0_55) ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_3803,c_45]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_3977,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 11.12/2.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 11.12/2.02      | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 11.12/2.02      inference(demodulation,[status(thm)],[c_3610,c_3933,c_3937]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8609,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 11.12/2.02      | k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 11.12/2.02      | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 11.12/2.02      inference(demodulation,[status(thm)],[c_8606,c_3977]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_8610,plain,
% 11.12/2.02      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 11.12/2.02      | k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 11.12/2.02      | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 11.12/2.02      inference(demodulation,[status(thm)],[c_8609,c_8606]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_20,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_1(X3)
% 11.12/2.02      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X1)
% 11.12/2.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.12/2.02      inference(cnf_transformation,[],[f102]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_22,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_1(X3)
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X1) ),
% 11.12/2.02      inference(cnf_transformation,[],[f80]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_202,plain,
% 11.12/2.02      ( ~ v1_funct_1(X3)
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X1)
% 11.12/2.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_20,c_23,c_22,c_21]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_203,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_1(X3)
% 11.12/2.02      | v1_xboole_0(X1)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.12/2.02      inference(renaming,[status(thm)],[c_202]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1126,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 11.12/2.02      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 11.12/2.02      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 11.12/2.02      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 11.12/2.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 11.12/2.02      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 11.12/2.02      | ~ v1_funct_1(X0_55)
% 11.12/2.02      | ~ v1_funct_1(X3_55)
% 11.12/2.02      | v1_xboole_0(X1_55)
% 11.12/2.02      | v1_xboole_0(X2_55)
% 11.12/2.02      | v1_xboole_0(X4_55)
% 11.12/2.02      | v1_xboole_0(X5_55)
% 11.12/2.02      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_203]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2025,plain,
% 11.12/2.02      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
% 11.12/2.02      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 11.12/2.02      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 11.12/2.02      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 11.12/2.02      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 11.12/2.02      | v1_funct_1(X2_55) != iProver_top
% 11.12/2.02      | v1_funct_1(X5_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(X3_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X4_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X1_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_4511,plain,
% 11.12/2.02      ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
% 11.12/2.02      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 11.12/2.02      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(X1_55) != iProver_top
% 11.12/2.02      | v1_funct_1(sK7) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(sK3) = iProver_top
% 11.12/2.02      | v1_xboole_0(sK5) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_3933,c_2025]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_50,plain,
% 11.12/2.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_5936,plain,
% 11.12/2.02      ( v1_funct_1(X1_55) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 11.12/2.02      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
% 11.12/2.02      | k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_4511,c_39,c_42,c_48,c_49,c_50]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_5937,plain,
% 11.12/2.02      ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
% 11.12/2.02      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(X1_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top ),
% 11.12/2.02      inference(renaming,[status(thm)],[c_5936]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_5943,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 11.12/2.02      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 11.12/2.02      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(sK6) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(sK4) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_3937,c_5937]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_47,plain,
% 11.12/2.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2185,plain,
% 11.12/2.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0_55))
% 11.12/2.02      | ~ v1_xboole_0(X0_55)
% 11.12/2.02      | v1_xboole_0(sK4) ),
% 11.12/2.02      inference(instantiation,[status(thm)],[c_1148]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2186,plain,
% 11.12/2.02      ( m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(sK4) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_2185]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6024,plain,
% 11.12/2.02      ( m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_5943,c_40,c_45,c_46,c_47,c_2186]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6025,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 11.12/2.02      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
% 11.12/2.02      inference(renaming,[status(thm)],[c_6024]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6030,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 11.12/2.02      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_3157,c_6025]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6031,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 11.12/2.02      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(light_normalisation,[status(thm)],[c_6030,c_3080]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6032,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 11.12/2.02      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0)
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(demodulation,[status(thm)],[c_6031,c_3157]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6033,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 11.12/2.02      | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(light_normalisation,[status(thm)],[c_6032,c_3080]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6034,plain,
% 11.12/2.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 11.12/2.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 11.12/2.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 11.12/2.02      | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 11.12/2.02      inference(predicate_to_equality_rev,[status(thm)],[c_6033]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_19,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_1(X3)
% 11.12/2.02      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X1)
% 11.12/2.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.12/2.02      inference(cnf_transformation,[],[f101]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_209,plain,
% 11.12/2.02      ( ~ v1_funct_1(X3)
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X1)
% 11.12/2.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_19,c_23,c_22,c_21]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_210,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0,X1,X2)
% 11.12/2.02      | ~ v1_funct_2(X3,X4,X2)
% 11.12/2.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.12/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.12/2.02      | ~ v1_funct_1(X0)
% 11.12/2.02      | ~ v1_funct_1(X3)
% 11.12/2.02      | v1_xboole_0(X1)
% 11.12/2.02      | v1_xboole_0(X2)
% 11.12/2.02      | v1_xboole_0(X4)
% 11.12/2.02      | v1_xboole_0(X5)
% 11.12/2.02      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.12/2.02      inference(renaming,[status(thm)],[c_209]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_1125,plain,
% 11.12/2.02      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 11.12/2.02      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 11.12/2.02      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 11.12/2.02      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 11.12/2.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 11.12/2.02      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 11.12/2.02      | ~ v1_funct_1(X0_55)
% 11.12/2.02      | ~ v1_funct_1(X3_55)
% 11.12/2.02      | v1_xboole_0(X1_55)
% 11.12/2.02      | v1_xboole_0(X2_55)
% 11.12/2.02      | v1_xboole_0(X4_55)
% 11.12/2.02      | v1_xboole_0(X5_55)
% 11.12/2.02      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
% 11.12/2.02      inference(subtyping,[status(esa)],[c_210]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_2026,plain,
% 11.12/2.02      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
% 11.12/2.02      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 11.12/2.02      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 11.12/2.02      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 11.12/2.02      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 11.12/2.02      | v1_funct_1(X2_55) != iProver_top
% 11.12/2.02      | v1_funct_1(X5_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(X3_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X4_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X1_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top ),
% 11.12/2.02      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6220,plain,
% 11.12/2.02      ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
% 11.12/2.02      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 11.12/2.02      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(X1_55) != iProver_top
% 11.12/2.02      | v1_funct_1(sK7) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(sK3) = iProver_top
% 11.12/2.02      | v1_xboole_0(sK5) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_3933,c_2026]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6886,plain,
% 11.12/2.02      ( v1_funct_1(X1_55) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 11.12/2.02      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
% 11.12/2.02      | k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_6220,c_39,c_42,c_48,c_49,c_50]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6887,plain,
% 11.12/2.02      ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
% 11.12/2.02      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(X1_55) != iProver_top
% 11.12/2.02      | v1_xboole_0(X2_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top ),
% 11.12/2.02      inference(renaming,[status(thm)],[c_6886]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6893,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 11.12/2.02      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 11.12/2.02      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 11.12/2.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | v1_funct_1(sK6) != iProver_top
% 11.12/2.02      | v1_xboole_0(X0_55) = iProver_top
% 11.12/2.02      | v1_xboole_0(sK4) = iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_3937,c_6887]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6926,plain,
% 11.12/2.02      ( m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 11.12/2.02      | k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_6893,c_40,c_45,c_46,c_47,c_2186]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6927,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 11.12/2.02      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
% 11.12/2.02      inference(renaming,[status(thm)],[c_6926]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6932,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 11.12/2.02      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(superposition,[status(thm)],[c_3157,c_6927]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6933,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 11.12/2.02      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(light_normalisation,[status(thm)],[c_6932,c_3080]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6934,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 11.12/2.02      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0)
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(demodulation,[status(thm)],[c_6933,c_3157]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6935,plain,
% 11.12/2.02      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 11.12/2.02      | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0)
% 11.12/2.02      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 11.12/2.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.12/2.02      inference(light_normalisation,[status(thm)],[c_6934,c_3080]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_6936,plain,
% 11.12/2.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 11.12/2.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 11.12/2.02      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 11.12/2.02      | k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 11.12/2.02      inference(predicate_to_equality_rev,[status(thm)],[c_6935]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_9743,plain,
% 11.12/2.02      ( k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 11.12/2.02      inference(global_propositional_subsumption,
% 11.12/2.02                [status(thm)],
% 11.12/2.02                [c_8610,c_34,c_32,c_3977,c_6034,c_6936]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(c_11278,plain,
% 11.12/2.02      ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 11.12/2.02      inference(demodulation,[status(thm)],[c_11253,c_9743]) ).
% 11.12/2.02  
% 11.12/2.02  cnf(contradiction,plain,
% 11.12/2.02      ( $false ),
% 11.12/2.02      inference(minisat,[status(thm)],[c_13113,c_11278]) ).
% 11.12/2.02  
% 11.12/2.02  
% 11.12/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.12/2.02  
% 11.12/2.02  ------                               Statistics
% 11.12/2.02  
% 11.12/2.02  ------ General
% 11.12/2.02  
% 11.12/2.02  abstr_ref_over_cycles:                  0
% 11.12/2.02  abstr_ref_under_cycles:                 0
% 11.12/2.02  gc_basic_clause_elim:                   0
% 11.12/2.02  forced_gc_time:                         0
% 11.12/2.02  parsing_time:                           0.016
% 11.12/2.02  unif_index_cands_time:                  0.
% 11.12/2.02  unif_index_add_time:                    0.
% 11.12/2.02  orderings_time:                         0.
% 11.12/2.02  out_proof_time:                         0.031
% 11.12/2.02  total_time:                             1.348
% 11.12/2.02  num_of_symbols:                         62
% 11.12/2.02  num_of_terms:                           37323
% 11.12/2.02  
% 11.12/2.02  ------ Preprocessing
% 11.12/2.02  
% 11.12/2.02  num_of_splits:                          0
% 11.12/2.02  num_of_split_atoms:                     0
% 11.12/2.02  num_of_reused_defs:                     0
% 11.12/2.02  num_eq_ax_congr_red:                    25
% 11.12/2.02  num_of_sem_filtered_clauses:            1
% 11.12/2.02  num_of_subtypes:                        4
% 11.12/2.02  monotx_restored_types:                  0
% 11.12/2.02  sat_num_of_epr_types:                   0
% 11.12/2.02  sat_num_of_non_cyclic_types:            0
% 11.12/2.02  sat_guarded_non_collapsed_types:        1
% 11.12/2.02  num_pure_diseq_elim:                    0
% 11.12/2.02  simp_replaced_by:                       0
% 11.12/2.02  res_preprocessed:                       184
% 11.12/2.02  prep_upred:                             0
% 11.12/2.02  prep_unflattend:                        14
% 11.12/2.02  smt_new_axioms:                         0
% 11.12/2.02  pred_elim_cands:                        7
% 11.12/2.02  pred_elim:                              2
% 11.12/2.02  pred_elim_cl:                           3
% 11.12/2.02  pred_elim_cycles:                       4
% 11.12/2.02  merged_defs:                            8
% 11.12/2.02  merged_defs_ncl:                        0
% 11.12/2.02  bin_hyper_res:                          8
% 11.12/2.02  prep_cycles:                            4
% 11.12/2.02  pred_elim_time:                         0.007
% 11.12/2.02  splitting_time:                         0.
% 11.12/2.02  sem_filter_time:                        0.
% 11.12/2.02  monotx_time:                            0.
% 11.12/2.02  subtype_inf_time:                       0.001
% 11.12/2.02  
% 11.12/2.02  ------ Problem properties
% 11.12/2.02  
% 11.12/2.02  clauses:                                35
% 11.12/2.02  conjectures:                            13
% 11.12/2.02  epr:                                    12
% 11.12/2.02  horn:                                   26
% 11.12/2.02  ground:                                 15
% 11.12/2.02  unary:                                  15
% 11.12/2.02  binary:                                 7
% 11.12/2.02  lits:                                   134
% 11.12/2.02  lits_eq:                                15
% 11.12/2.02  fd_pure:                                0
% 11.12/2.02  fd_pseudo:                              0
% 11.12/2.02  fd_cond:                                0
% 11.12/2.02  fd_pseudo_cond:                         0
% 11.12/2.02  ac_symbols:                             0
% 11.12/2.02  
% 11.12/2.02  ------ Propositional Solver
% 11.12/2.02  
% 11.12/2.02  prop_solver_calls:                      30
% 11.12/2.02  prop_fast_solver_calls:                 3970
% 11.12/2.02  smt_solver_calls:                       0
% 11.12/2.02  smt_fast_solver_calls:                  0
% 11.12/2.02  prop_num_of_clauses:                    7349
% 11.12/2.02  prop_preprocess_simplified:             15354
% 11.12/2.02  prop_fo_subsumed:                       371
% 11.12/2.02  prop_solver_time:                       0.
% 11.12/2.02  smt_solver_time:                        0.
% 11.12/2.02  smt_fast_solver_time:                   0.
% 11.12/2.02  prop_fast_solver_time:                  0.
% 11.12/2.02  prop_unsat_core_time:                   0.001
% 11.12/2.02  
% 11.12/2.02  ------ QBF
% 11.12/2.02  
% 11.12/2.02  qbf_q_res:                              0
% 11.12/2.02  qbf_num_tautologies:                    0
% 11.12/2.02  qbf_prep_cycles:                        0
% 11.12/2.02  
% 11.12/2.02  ------ BMC1
% 11.12/2.02  
% 11.12/2.02  bmc1_current_bound:                     -1
% 11.12/2.02  bmc1_last_solved_bound:                 -1
% 11.12/2.02  bmc1_unsat_core_size:                   -1
% 11.12/2.02  bmc1_unsat_core_parents_size:           -1
% 11.12/2.02  bmc1_merge_next_fun:                    0
% 11.12/2.02  bmc1_unsat_core_clauses_time:           0.
% 11.12/2.02  
% 11.12/2.02  ------ Instantiation
% 11.12/2.02  
% 11.12/2.02  inst_num_of_clauses:                    1644
% 11.12/2.02  inst_num_in_passive:                    393
% 11.12/2.02  inst_num_in_active:                     992
% 11.12/2.02  inst_num_in_unprocessed:                259
% 11.12/2.02  inst_num_of_loops:                      1170
% 11.12/2.02  inst_num_of_learning_restarts:          0
% 11.12/2.02  inst_num_moves_active_passive:          175
% 11.12/2.02  inst_lit_activity:                      0
% 11.12/2.02  inst_lit_activity_moves:                1
% 11.12/2.02  inst_num_tautologies:                   0
% 11.12/2.02  inst_num_prop_implied:                  0
% 11.12/2.02  inst_num_existing_simplified:           0
% 11.12/2.02  inst_num_eq_res_simplified:             0
% 11.12/2.02  inst_num_child_elim:                    0
% 11.12/2.02  inst_num_of_dismatching_blockings:      117
% 11.12/2.02  inst_num_of_non_proper_insts:           1653
% 11.12/2.02  inst_num_of_duplicates:                 0
% 11.12/2.02  inst_inst_num_from_inst_to_res:         0
% 11.12/2.02  inst_dismatching_checking_time:         0.
% 11.12/2.02  
% 11.12/2.02  ------ Resolution
% 11.12/2.02  
% 11.12/2.02  res_num_of_clauses:                     0
% 11.12/2.02  res_num_in_passive:                     0
% 11.12/2.02  res_num_in_active:                      0
% 11.12/2.02  res_num_of_loops:                       188
% 11.12/2.02  res_forward_subset_subsumed:            49
% 11.12/2.02  res_backward_subset_subsumed:           0
% 11.12/2.02  res_forward_subsumed:                   0
% 11.12/2.02  res_backward_subsumed:                  0
% 11.12/2.02  res_forward_subsumption_resolution:     0
% 11.12/2.02  res_backward_subsumption_resolution:    0
% 11.12/2.02  res_clause_to_clause_subsumption:       1011
% 11.12/2.02  res_orphan_elimination:                 0
% 11.12/2.02  res_tautology_del:                      30
% 11.12/2.02  res_num_eq_res_simplified:              0
% 11.12/2.02  res_num_sel_changes:                    0
% 11.12/2.02  res_moves_from_active_to_pass:          0
% 11.12/2.02  
% 11.12/2.02  ------ Superposition
% 11.12/2.02  
% 11.12/2.02  sup_time_total:                         0.
% 11.12/2.02  sup_time_generating:                    0.
% 11.12/2.02  sup_time_sim_full:                      0.
% 11.12/2.02  sup_time_sim_immed:                     0.
% 11.12/2.02  
% 11.12/2.02  sup_num_of_clauses:                     337
% 11.12/2.02  sup_num_in_active:                      207
% 11.12/2.02  sup_num_in_passive:                     130
% 11.12/2.02  sup_num_of_loops:                       232
% 11.12/2.02  sup_fw_superposition:                   251
% 11.12/2.02  sup_bw_superposition:                   183
% 11.12/2.02  sup_immediate_simplified:               184
% 11.12/2.02  sup_given_eliminated:                   0
% 11.12/2.02  comparisons_done:                       0
% 11.12/2.02  comparisons_avoided:                    0
% 11.12/2.02  
% 11.12/2.02  ------ Simplifications
% 11.12/2.02  
% 11.12/2.02  
% 11.12/2.02  sim_fw_subset_subsumed:                 34
% 11.12/2.02  sim_bw_subset_subsumed:                 0
% 11.12/2.02  sim_fw_subsumed:                        27
% 11.12/2.02  sim_bw_subsumed:                        17
% 11.12/2.02  sim_fw_subsumption_res:                 0
% 11.12/2.02  sim_bw_subsumption_res:                 0
% 11.12/2.02  sim_tautology_del:                      1
% 11.12/2.02  sim_eq_tautology_del:                   8
% 11.12/2.02  sim_eq_res_simp:                        0
% 11.12/2.02  sim_fw_demodulated:                     94
% 11.12/2.02  sim_bw_demodulated:                     9
% 11.12/2.02  sim_light_normalised:                   56
% 11.12/2.02  sim_joinable_taut:                      0
% 11.12/2.02  sim_joinable_simp:                      0
% 11.12/2.02  sim_ac_normalised:                      0
% 11.12/2.02  sim_smt_subsumption:                    0
% 11.12/2.02  
%------------------------------------------------------------------------------
