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
% DateTime   : Thu Dec  3 12:21:34 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :  217 (2248 expanded)
%              Number of clauses        :  145 ( 589 expanded)
%              Number of leaves         :   19 ( 881 expanded)
%              Depth                    :   23
%              Number of atoms          : 1225 (29200 expanded)
%              Number of equality atoms :  491 (6952 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f51,f50,f49,f48,f47,f46])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f74,plain,(
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

fof(f75,plain,(
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

fof(f76,plain,(
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

fof(f78,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f90,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1230,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2038,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1245,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | k9_subset_1(X1_56,X2_56,X0_56) = k3_xboole_0(X2_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2024,plain,
    ( k9_subset_1(X0_56,X1_56,X2_56) = k3_xboole_0(X1_56,X2_56)
    | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_2630,plain,
    ( k9_subset_1(sK1,X0_56,sK4) = k3_xboole_0(X0_56,sK4) ),
    inference(superposition,[status(thm)],[c_2038,c_2024])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1233,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2035,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1242,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | k2_partfun1(X1_56,X2_56,X0_56,X3_56) = k7_relat_1(X0_56,X3_56) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2027,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,X3_56) = k7_relat_1(X2_56,X3_56)
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_3373,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0_56) = k7_relat_1(sK5,X0_56)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2035,c_2027])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2465,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_56,X1_56,sK5,X2_56) = k7_relat_1(sK5,X2_56) ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_2658,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK2,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
    inference(instantiation,[status(thm)],[c_2465])).

cnf(c_4088,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_30,c_28,c_2658])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1236,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2032,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_3372,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0_56) = k7_relat_1(sK6,X0_56)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_2027])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2460,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0_56,X1_56,sK6,X2_56) = k7_relat_1(sK6,X2_56) ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_2653,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK2,sK6,X0_56) = k7_relat_1(sK6,X0_56) ),
    inference(instantiation,[status(thm)],[c_2460])).

cnf(c_3702,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0_56) = k7_relat_1(sK6,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3372,c_27,c_25,c_2653])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f94])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_215,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_23,c_22,c_21])).

cnf(c_216,plain,
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
    inference(renaming,[status(thm)],[c_215])).

cnf(c_1223,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ v1_funct_2(X3_56,X4_56,X2_56)
    | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X3_56)
    | v1_xboole_0(X2_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X4_56)
    | v1_xboole_0(X5_56)
    | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
    | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X1_56) = X0_56 ),
    inference(subtyping,[status(esa)],[c_216])).

cnf(c_2045,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
    | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X0_56) = X2_56
    | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
    | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
    | v1_funct_1(X2_56) != iProver_top
    | v1_funct_1(X5_56) != iProver_top
    | v1_xboole_0(X3_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X4_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1223])).

cnf(c_7923,plain,
    ( k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
    | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),sK4) = sK6
    | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(X2_56) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_2045])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_42,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_48,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_49,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_50,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18283,plain,
    ( v1_funct_1(X1_56) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),sK4) = sK6
    | k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(X2_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7923,c_39,c_42,c_48,c_49,c_50])).

cnf(c_18284,plain,
    ( k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
    | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),sK4) = sK6
    | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_xboole_0(X2_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_18283])).

cnf(c_18299,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_18284])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18474,plain,
    ( v1_xboole_0(X0_56) = iProver_top
    | k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18299,c_40,c_45,c_46,c_47])).

cnf(c_18475,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_18474])).

cnf(c_18485,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2630,c_18475])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_31,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_565,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_566,plain,
    ( r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_568,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_35,c_33])).

cnf(c_1221,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_568])).

cnf(c_2047,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1221])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1249,plain,
    ( ~ r1_xboole_0(X0_56,X1_56)
    | k3_xboole_0(X0_56,X1_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2020,plain,
    ( k3_xboole_0(X0_56,X1_56) = k1_xboole_0
    | r1_xboole_0(X0_56,X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_3039,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2047,c_2020])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1243,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2026,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
    | v1_relat_1(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1243])).

cnf(c_2975,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_2026])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1246,plain,
    ( r2_hidden(sK0(X0_56,X1_56),X0_56)
    | r1_xboole_0(X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2023,plain,
    ( r2_hidden(sK0(X0_56,X1_56),X0_56) = iProver_top
    | r1_xboole_0(X0_56,X1_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_491,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_492,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_1222,plain,
    ( ~ r2_hidden(X0_58,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_492])).

cnf(c_2046,plain,
    ( r2_hidden(X0_58,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1222])).

cnf(c_3088,plain,
    ( r1_xboole_0(k1_xboole_0,X0_56) = iProver_top ),
    inference(superposition,[status(thm)],[c_2023,c_2046])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1244,plain,
    ( ~ r1_xboole_0(X0_56,k1_relat_1(X1_56))
    | ~ v1_relat_1(X1_56)
    | k7_relat_1(X1_56,X0_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2025,plain,
    ( k7_relat_1(X0_56,X1_56) = k1_xboole_0
    | r1_xboole_0(X1_56,k1_relat_1(X0_56)) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_3392,plain,
    ( k7_relat_1(X0_56,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_2025])).

cnf(c_4174,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2975,c_3392])).

cnf(c_18486,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18485,c_3039,c_4174])).

cnf(c_1240,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ v1_funct_2(X3_56,X4_56,X2_56)
    | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
    | m1_subset_1(k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_56,X4_56,X1_56),X2_56)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X3_56)
    | v1_xboole_0(X2_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X4_56)
    | v1_xboole_0(X5_56) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2029,plain,
    ( v1_funct_2(X0_56,X1_56,X2_56) != iProver_top
    | v1_funct_2(X3_56,X4_56,X2_56) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(X5_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(X5_56)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
    | m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_56,X4_56,X1_56),X2_56))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X3_56) != iProver_top
    | v1_xboole_0(X5_56) = iProver_top
    | v1_xboole_0(X2_56) = iProver_top
    | v1_xboole_0(X4_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_4919,plain,
    ( k2_partfun1(k4_subset_1(X0_56,X1_56,X2_56),X3_56,k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56),X6_56) = k7_relat_1(k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56),X6_56)
    | v1_funct_2(X5_56,X2_56,X3_56) != iProver_top
    | v1_funct_2(X4_56,X1_56,X3_56) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X2_56,X3_56))) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X3_56))) != iProver_top
    | v1_funct_1(X5_56) != iProver_top
    | v1_funct_1(X4_56) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56)) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(X3_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X2_56) = iProver_top ),
    inference(superposition,[status(thm)],[c_2029,c_2027])).

cnf(c_1238,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ v1_funct_2(X3_56,X4_56,X2_56)
    | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X3_56)
    | v1_funct_1(k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56))
    | v1_xboole_0(X2_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X4_56)
    | v1_xboole_0(X5_56) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2031,plain,
    ( v1_funct_2(X0_56,X1_56,X2_56) != iProver_top
    | v1_funct_2(X3_56,X4_56,X2_56) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(X5_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(X5_56)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
    | m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X3_56) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56)) = iProver_top
    | v1_xboole_0(X5_56) = iProver_top
    | v1_xboole_0(X2_56) = iProver_top
    | v1_xboole_0(X4_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_8747,plain,
    ( k2_partfun1(k4_subset_1(X0_56,X1_56,X2_56),X3_56,k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56),X6_56) = k7_relat_1(k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56),X6_56)
    | v1_funct_2(X5_56,X2_56,X3_56) != iProver_top
    | v1_funct_2(X4_56,X1_56,X3_56) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X2_56,X3_56))) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X3_56))) != iProver_top
    | v1_funct_1(X5_56) != iProver_top
    | v1_funct_1(X4_56) != iProver_top
    | v1_xboole_0(X2_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X3_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4919,c_2031])).

cnf(c_8751,plain,
    ( k2_partfun1(k4_subset_1(X0_56,X1_56,sK4),sK2,k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56)
    | v1_funct_2(X2_56,X1_56,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(X2_56) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_8747])).

cnf(c_8931,plain,
    ( v1_funct_1(X2_56) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,sK2))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_56,X1_56,sK4),sK2,k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56)
    | v1_funct_2(X2_56,X1_56,sK2) != iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8751,c_39,c_42,c_48,c_49])).

cnf(c_8932,plain,
    ( k2_partfun1(k4_subset_1(X0_56,X1_56,sK4),sK2,k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56)
    | v1_funct_2(X2_56,X1_56,sK2) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(X2_56) != iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_8931])).

cnf(c_8946,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2035,c_8932])).

cnf(c_9910,plain,
    ( v1_xboole_0(X0_56) = iProver_top
    | k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56)
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8946,c_40,c_45,c_46])).

cnf(c_9911,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56)
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_9910])).

cnf(c_9920,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0_56) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0_56)
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_9911])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_38,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9992,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0_56) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9920,c_38,c_41])).

cnf(c_18487,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18486,c_2630,c_9992])).

cnf(c_2976,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2035,c_2026])).

cnf(c_4175,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2976,c_3392])).

cnf(c_18488,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18487,c_3039,c_4175])).

cnf(c_18489,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18488])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_208,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_23,c_22,c_21])).

cnf(c_209,plain,
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
    inference(renaming,[status(thm)],[c_208])).

cnf(c_1224,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ v1_funct_2(X3_56,X4_56,X2_56)
    | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X3_56)
    | v1_xboole_0(X2_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X4_56)
    | v1_xboole_0(X5_56)
    | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
    | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X4_56) = X3_56 ),
    inference(subtyping,[status(esa)],[c_209])).

cnf(c_2044,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
    | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X4_56) = X5_56
    | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
    | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
    | v1_funct_1(X2_56) != iProver_top
    | v1_funct_1(X5_56) != iProver_top
    | v1_xboole_0(X3_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X4_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1224])).

cnf(c_5869,plain,
    ( k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
    | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),X0_56) = X1_56
    | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(X2_56) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_2044])).

cnf(c_11253,plain,
    ( v1_funct_1(X1_56) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),X0_56) = X1_56
    | k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(X2_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5869,c_39,c_42,c_48,c_49,c_50])).

cnf(c_11254,plain,
    ( k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
    | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),X0_56) = X1_56
    | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_xboole_0(X2_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_11253])).

cnf(c_11269,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_11254])).

cnf(c_11553,plain,
    ( v1_xboole_0(X0_56) = iProver_top
    | k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11269,c_40,c_45,c_46,c_47])).

cnf(c_11554,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_11553])).

cnf(c_11564,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2630,c_11554])).

cnf(c_11565,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11564,c_3039,c_4174])).

cnf(c_11566,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11565,c_2630,c_9992])).

cnf(c_11567,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11566,c_3039,c_4175])).

cnf(c_11568,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11567])).

cnf(c_24,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1237,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2817,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK4,sK2,sK6,k3_xboole_0(sK3,sK4)) != k2_partfun1(sK3,sK2,sK5,k3_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_2630,c_1237])).

cnf(c_3230,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3039,c_2817])).

cnf(c_3706,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3702,c_3230])).

cnf(c_4092,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3706,c_4088])).

cnf(c_4181,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4174,c_4092])).

cnf(c_2377,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_2544,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0_56),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X0_56) ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_2892,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK5)),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2544])).

cnf(c_2585,plain,
    ( ~ r1_xboole_0(X0_56,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,X0_56) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_2893,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2585])).

cnf(c_2545,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,X0_56),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_3358,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK5)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_4240,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4181,c_28,c_2377,c_2892,c_2893,c_3358])).

cnf(c_4241,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 ),
    inference(renaming,[status(thm)],[c_4240])).

cnf(c_9996,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 ),
    inference(demodulation,[status(thm)],[c_9992,c_4241])).

cnf(c_9997,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_9996,c_9992])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18489,c_11568,c_9997,c_43,c_41,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:27:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.27/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.27/1.48  
% 7.27/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.27/1.48  
% 7.27/1.48  ------  iProver source info
% 7.27/1.48  
% 7.27/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.27/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.27/1.48  git: non_committed_changes: false
% 7.27/1.48  git: last_make_outside_of_git: false
% 7.27/1.48  
% 7.27/1.48  ------ 
% 7.27/1.48  
% 7.27/1.48  ------ Input Options
% 7.27/1.48  
% 7.27/1.48  --out_options                           all
% 7.27/1.48  --tptp_safe_out                         true
% 7.27/1.48  --problem_path                          ""
% 7.27/1.48  --include_path                          ""
% 7.27/1.48  --clausifier                            res/vclausify_rel
% 7.27/1.48  --clausifier_options                    --mode clausify
% 7.27/1.48  --stdin                                 false
% 7.27/1.48  --stats_out                             all
% 7.27/1.48  
% 7.27/1.48  ------ General Options
% 7.27/1.48  
% 7.27/1.48  --fof                                   false
% 7.27/1.48  --time_out_real                         305.
% 7.27/1.48  --time_out_virtual                      -1.
% 7.27/1.48  --symbol_type_check                     false
% 7.27/1.48  --clausify_out                          false
% 7.27/1.48  --sig_cnt_out                           false
% 7.27/1.48  --trig_cnt_out                          false
% 7.27/1.48  --trig_cnt_out_tolerance                1.
% 7.27/1.48  --trig_cnt_out_sk_spl                   false
% 7.27/1.48  --abstr_cl_out                          false
% 7.27/1.48  
% 7.27/1.48  ------ Global Options
% 7.27/1.48  
% 7.27/1.48  --schedule                              default
% 7.27/1.48  --add_important_lit                     false
% 7.27/1.48  --prop_solver_per_cl                    1000
% 7.27/1.48  --min_unsat_core                        false
% 7.27/1.48  --soft_assumptions                      false
% 7.27/1.48  --soft_lemma_size                       3
% 7.27/1.48  --prop_impl_unit_size                   0
% 7.27/1.48  --prop_impl_unit                        []
% 7.27/1.48  --share_sel_clauses                     true
% 7.27/1.48  --reset_solvers                         false
% 7.27/1.48  --bc_imp_inh                            [conj_cone]
% 7.27/1.48  --conj_cone_tolerance                   3.
% 7.27/1.48  --extra_neg_conj                        none
% 7.27/1.48  --large_theory_mode                     true
% 7.27/1.48  --prolific_symb_bound                   200
% 7.27/1.48  --lt_threshold                          2000
% 7.27/1.48  --clause_weak_htbl                      true
% 7.27/1.48  --gc_record_bc_elim                     false
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing Options
% 7.27/1.48  
% 7.27/1.48  --preprocessing_flag                    true
% 7.27/1.48  --time_out_prep_mult                    0.1
% 7.27/1.48  --splitting_mode                        input
% 7.27/1.48  --splitting_grd                         true
% 7.27/1.48  --splitting_cvd                         false
% 7.27/1.48  --splitting_cvd_svl                     false
% 7.27/1.48  --splitting_nvd                         32
% 7.27/1.48  --sub_typing                            true
% 7.27/1.48  --prep_gs_sim                           true
% 7.27/1.48  --prep_unflatten                        true
% 7.27/1.48  --prep_res_sim                          true
% 7.27/1.48  --prep_upred                            true
% 7.27/1.48  --prep_sem_filter                       exhaustive
% 7.27/1.48  --prep_sem_filter_out                   false
% 7.27/1.48  --pred_elim                             true
% 7.27/1.48  --res_sim_input                         true
% 7.27/1.48  --eq_ax_congr_red                       true
% 7.27/1.48  --pure_diseq_elim                       true
% 7.27/1.48  --brand_transform                       false
% 7.27/1.48  --non_eq_to_eq                          false
% 7.27/1.48  --prep_def_merge                        true
% 7.27/1.48  --prep_def_merge_prop_impl              false
% 7.27/1.48  --prep_def_merge_mbd                    true
% 7.27/1.48  --prep_def_merge_tr_red                 false
% 7.27/1.48  --prep_def_merge_tr_cl                  false
% 7.27/1.48  --smt_preprocessing                     true
% 7.27/1.48  --smt_ac_axioms                         fast
% 7.27/1.48  --preprocessed_out                      false
% 7.27/1.48  --preprocessed_stats                    false
% 7.27/1.48  
% 7.27/1.48  ------ Abstraction refinement Options
% 7.27/1.48  
% 7.27/1.48  --abstr_ref                             []
% 7.27/1.48  --abstr_ref_prep                        false
% 7.27/1.48  --abstr_ref_until_sat                   false
% 7.27/1.48  --abstr_ref_sig_restrict                funpre
% 7.27/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.27/1.48  --abstr_ref_under                       []
% 7.27/1.48  
% 7.27/1.48  ------ SAT Options
% 7.27/1.48  
% 7.27/1.48  --sat_mode                              false
% 7.27/1.48  --sat_fm_restart_options                ""
% 7.27/1.48  --sat_gr_def                            false
% 7.27/1.48  --sat_epr_types                         true
% 7.27/1.48  --sat_non_cyclic_types                  false
% 7.27/1.48  --sat_finite_models                     false
% 7.27/1.48  --sat_fm_lemmas                         false
% 7.27/1.48  --sat_fm_prep                           false
% 7.27/1.48  --sat_fm_uc_incr                        true
% 7.27/1.48  --sat_out_model                         small
% 7.27/1.48  --sat_out_clauses                       false
% 7.27/1.48  
% 7.27/1.48  ------ QBF Options
% 7.27/1.48  
% 7.27/1.48  --qbf_mode                              false
% 7.27/1.48  --qbf_elim_univ                         false
% 7.27/1.48  --qbf_dom_inst                          none
% 7.27/1.48  --qbf_dom_pre_inst                      false
% 7.27/1.48  --qbf_sk_in                             false
% 7.27/1.48  --qbf_pred_elim                         true
% 7.27/1.48  --qbf_split                             512
% 7.27/1.48  
% 7.27/1.48  ------ BMC1 Options
% 7.27/1.48  
% 7.27/1.48  --bmc1_incremental                      false
% 7.27/1.48  --bmc1_axioms                           reachable_all
% 7.27/1.48  --bmc1_min_bound                        0
% 7.27/1.48  --bmc1_max_bound                        -1
% 7.27/1.48  --bmc1_max_bound_default                -1
% 7.27/1.48  --bmc1_symbol_reachability              true
% 7.27/1.48  --bmc1_property_lemmas                  false
% 7.27/1.48  --bmc1_k_induction                      false
% 7.27/1.48  --bmc1_non_equiv_states                 false
% 7.27/1.48  --bmc1_deadlock                         false
% 7.27/1.48  --bmc1_ucm                              false
% 7.27/1.48  --bmc1_add_unsat_core                   none
% 7.27/1.48  --bmc1_unsat_core_children              false
% 7.27/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.27/1.48  --bmc1_out_stat                         full
% 7.27/1.48  --bmc1_ground_init                      false
% 7.27/1.48  --bmc1_pre_inst_next_state              false
% 7.27/1.48  --bmc1_pre_inst_state                   false
% 7.27/1.48  --bmc1_pre_inst_reach_state             false
% 7.27/1.48  --bmc1_out_unsat_core                   false
% 7.27/1.48  --bmc1_aig_witness_out                  false
% 7.27/1.48  --bmc1_verbose                          false
% 7.27/1.48  --bmc1_dump_clauses_tptp                false
% 7.27/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.27/1.48  --bmc1_dump_file                        -
% 7.27/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.27/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.27/1.48  --bmc1_ucm_extend_mode                  1
% 7.27/1.48  --bmc1_ucm_init_mode                    2
% 7.27/1.48  --bmc1_ucm_cone_mode                    none
% 7.27/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.27/1.48  --bmc1_ucm_relax_model                  4
% 7.27/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.27/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.27/1.48  --bmc1_ucm_layered_model                none
% 7.27/1.48  --bmc1_ucm_max_lemma_size               10
% 7.27/1.48  
% 7.27/1.48  ------ AIG Options
% 7.27/1.48  
% 7.27/1.48  --aig_mode                              false
% 7.27/1.48  
% 7.27/1.48  ------ Instantiation Options
% 7.27/1.48  
% 7.27/1.48  --instantiation_flag                    true
% 7.27/1.48  --inst_sos_flag                         false
% 7.27/1.48  --inst_sos_phase                        true
% 7.27/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.27/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.27/1.48  --inst_lit_sel_side                     num_symb
% 7.27/1.48  --inst_solver_per_active                1400
% 7.27/1.48  --inst_solver_calls_frac                1.
% 7.27/1.48  --inst_passive_queue_type               priority_queues
% 7.27/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.27/1.48  --inst_passive_queues_freq              [25;2]
% 7.27/1.48  --inst_dismatching                      true
% 7.27/1.48  --inst_eager_unprocessed_to_passive     true
% 7.27/1.48  --inst_prop_sim_given                   true
% 7.27/1.48  --inst_prop_sim_new                     false
% 7.27/1.48  --inst_subs_new                         false
% 7.27/1.48  --inst_eq_res_simp                      false
% 7.27/1.48  --inst_subs_given                       false
% 7.27/1.48  --inst_orphan_elimination               true
% 7.27/1.48  --inst_learning_loop_flag               true
% 7.27/1.48  --inst_learning_start                   3000
% 7.27/1.48  --inst_learning_factor                  2
% 7.27/1.48  --inst_start_prop_sim_after_learn       3
% 7.27/1.48  --inst_sel_renew                        solver
% 7.27/1.48  --inst_lit_activity_flag                true
% 7.27/1.48  --inst_restr_to_given                   false
% 7.27/1.48  --inst_activity_threshold               500
% 7.27/1.48  --inst_out_proof                        true
% 7.27/1.48  
% 7.27/1.48  ------ Resolution Options
% 7.27/1.48  
% 7.27/1.48  --resolution_flag                       true
% 7.27/1.48  --res_lit_sel                           adaptive
% 7.27/1.48  --res_lit_sel_side                      none
% 7.27/1.48  --res_ordering                          kbo
% 7.27/1.48  --res_to_prop_solver                    active
% 7.27/1.48  --res_prop_simpl_new                    false
% 7.27/1.48  --res_prop_simpl_given                  true
% 7.27/1.48  --res_passive_queue_type                priority_queues
% 7.27/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.27/1.48  --res_passive_queues_freq               [15;5]
% 7.27/1.48  --res_forward_subs                      full
% 7.27/1.48  --res_backward_subs                     full
% 7.27/1.48  --res_forward_subs_resolution           true
% 7.27/1.48  --res_backward_subs_resolution          true
% 7.27/1.48  --res_orphan_elimination                true
% 7.27/1.48  --res_time_limit                        2.
% 7.27/1.48  --res_out_proof                         true
% 7.27/1.48  
% 7.27/1.48  ------ Superposition Options
% 7.27/1.48  
% 7.27/1.48  --superposition_flag                    true
% 7.27/1.48  --sup_passive_queue_type                priority_queues
% 7.27/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.27/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.27/1.48  --demod_completeness_check              fast
% 7.27/1.48  --demod_use_ground                      true
% 7.27/1.48  --sup_to_prop_solver                    passive
% 7.27/1.48  --sup_prop_simpl_new                    true
% 7.27/1.48  --sup_prop_simpl_given                  true
% 7.27/1.48  --sup_fun_splitting                     false
% 7.27/1.48  --sup_smt_interval                      50000
% 7.27/1.48  
% 7.27/1.48  ------ Superposition Simplification Setup
% 7.27/1.48  
% 7.27/1.48  --sup_indices_passive                   []
% 7.27/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.27/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_full_bw                           [BwDemod]
% 7.27/1.48  --sup_immed_triv                        [TrivRules]
% 7.27/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_immed_bw_main                     []
% 7.27/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.27/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.27/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.27/1.48  
% 7.27/1.48  ------ Combination Options
% 7.27/1.48  
% 7.27/1.48  --comb_res_mult                         3
% 7.27/1.48  --comb_sup_mult                         2
% 7.27/1.48  --comb_inst_mult                        10
% 7.27/1.48  
% 7.27/1.48  ------ Debug Options
% 7.27/1.48  
% 7.27/1.48  --dbg_backtrace                         false
% 7.27/1.48  --dbg_dump_prop_clauses                 false
% 7.27/1.48  --dbg_dump_prop_clauses_file            -
% 7.27/1.48  --dbg_out_stat                          false
% 7.27/1.48  ------ Parsing...
% 7.27/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.27/1.48  ------ Proving...
% 7.27/1.48  ------ Problem Properties 
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  clauses                                 31
% 7.27/1.48  conjectures                             13
% 7.27/1.48  EPR                                     11
% 7.27/1.48  Horn                                    22
% 7.27/1.48  unary                                   14
% 7.27/1.48  binary                                  6
% 7.27/1.48  lits                                    127
% 7.27/1.48  lits eq                                 15
% 7.27/1.48  fd_pure                                 0
% 7.27/1.48  fd_pseudo                               0
% 7.27/1.48  fd_cond                                 0
% 7.27/1.48  fd_pseudo_cond                          1
% 7.27/1.48  AC symbols                              0
% 7.27/1.48  
% 7.27/1.48  ------ Schedule dynamic 5 is on 
% 7.27/1.48  
% 7.27/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  ------ 
% 7.27/1.48  Current options:
% 7.27/1.48  ------ 
% 7.27/1.48  
% 7.27/1.48  ------ Input Options
% 7.27/1.48  
% 7.27/1.48  --out_options                           all
% 7.27/1.48  --tptp_safe_out                         true
% 7.27/1.48  --problem_path                          ""
% 7.27/1.48  --include_path                          ""
% 7.27/1.48  --clausifier                            res/vclausify_rel
% 7.27/1.48  --clausifier_options                    --mode clausify
% 7.27/1.48  --stdin                                 false
% 7.27/1.48  --stats_out                             all
% 7.27/1.48  
% 7.27/1.48  ------ General Options
% 7.27/1.48  
% 7.27/1.48  --fof                                   false
% 7.27/1.48  --time_out_real                         305.
% 7.27/1.48  --time_out_virtual                      -1.
% 7.27/1.48  --symbol_type_check                     false
% 7.27/1.48  --clausify_out                          false
% 7.27/1.48  --sig_cnt_out                           false
% 7.27/1.48  --trig_cnt_out                          false
% 7.27/1.48  --trig_cnt_out_tolerance                1.
% 7.27/1.48  --trig_cnt_out_sk_spl                   false
% 7.27/1.48  --abstr_cl_out                          false
% 7.27/1.48  
% 7.27/1.48  ------ Global Options
% 7.27/1.48  
% 7.27/1.48  --schedule                              default
% 7.27/1.48  --add_important_lit                     false
% 7.27/1.48  --prop_solver_per_cl                    1000
% 7.27/1.48  --min_unsat_core                        false
% 7.27/1.48  --soft_assumptions                      false
% 7.27/1.48  --soft_lemma_size                       3
% 7.27/1.48  --prop_impl_unit_size                   0
% 7.27/1.48  --prop_impl_unit                        []
% 7.27/1.48  --share_sel_clauses                     true
% 7.27/1.48  --reset_solvers                         false
% 7.27/1.48  --bc_imp_inh                            [conj_cone]
% 7.27/1.48  --conj_cone_tolerance                   3.
% 7.27/1.48  --extra_neg_conj                        none
% 7.27/1.48  --large_theory_mode                     true
% 7.27/1.48  --prolific_symb_bound                   200
% 7.27/1.48  --lt_threshold                          2000
% 7.27/1.48  --clause_weak_htbl                      true
% 7.27/1.48  --gc_record_bc_elim                     false
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing Options
% 7.27/1.48  
% 7.27/1.48  --preprocessing_flag                    true
% 7.27/1.48  --time_out_prep_mult                    0.1
% 7.27/1.48  --splitting_mode                        input
% 7.27/1.48  --splitting_grd                         true
% 7.27/1.48  --splitting_cvd                         false
% 7.27/1.48  --splitting_cvd_svl                     false
% 7.27/1.48  --splitting_nvd                         32
% 7.27/1.48  --sub_typing                            true
% 7.27/1.48  --prep_gs_sim                           true
% 7.27/1.48  --prep_unflatten                        true
% 7.27/1.48  --prep_res_sim                          true
% 7.27/1.48  --prep_upred                            true
% 7.27/1.48  --prep_sem_filter                       exhaustive
% 7.27/1.48  --prep_sem_filter_out                   false
% 7.27/1.48  --pred_elim                             true
% 7.27/1.48  --res_sim_input                         true
% 7.27/1.48  --eq_ax_congr_red                       true
% 7.27/1.48  --pure_diseq_elim                       true
% 7.27/1.48  --brand_transform                       false
% 7.27/1.48  --non_eq_to_eq                          false
% 7.27/1.48  --prep_def_merge                        true
% 7.27/1.48  --prep_def_merge_prop_impl              false
% 7.27/1.48  --prep_def_merge_mbd                    true
% 7.27/1.48  --prep_def_merge_tr_red                 false
% 7.27/1.48  --prep_def_merge_tr_cl                  false
% 7.27/1.48  --smt_preprocessing                     true
% 7.27/1.48  --smt_ac_axioms                         fast
% 7.27/1.48  --preprocessed_out                      false
% 7.27/1.48  --preprocessed_stats                    false
% 7.27/1.48  
% 7.27/1.48  ------ Abstraction refinement Options
% 7.27/1.48  
% 7.27/1.48  --abstr_ref                             []
% 7.27/1.48  --abstr_ref_prep                        false
% 7.27/1.48  --abstr_ref_until_sat                   false
% 7.27/1.48  --abstr_ref_sig_restrict                funpre
% 7.27/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.27/1.48  --abstr_ref_under                       []
% 7.27/1.48  
% 7.27/1.48  ------ SAT Options
% 7.27/1.48  
% 7.27/1.48  --sat_mode                              false
% 7.27/1.48  --sat_fm_restart_options                ""
% 7.27/1.48  --sat_gr_def                            false
% 7.27/1.48  --sat_epr_types                         true
% 7.27/1.48  --sat_non_cyclic_types                  false
% 7.27/1.48  --sat_finite_models                     false
% 7.27/1.48  --sat_fm_lemmas                         false
% 7.27/1.48  --sat_fm_prep                           false
% 7.27/1.48  --sat_fm_uc_incr                        true
% 7.27/1.48  --sat_out_model                         small
% 7.27/1.48  --sat_out_clauses                       false
% 7.27/1.48  
% 7.27/1.48  ------ QBF Options
% 7.27/1.48  
% 7.27/1.48  --qbf_mode                              false
% 7.27/1.48  --qbf_elim_univ                         false
% 7.27/1.48  --qbf_dom_inst                          none
% 7.27/1.48  --qbf_dom_pre_inst                      false
% 7.27/1.48  --qbf_sk_in                             false
% 7.27/1.48  --qbf_pred_elim                         true
% 7.27/1.48  --qbf_split                             512
% 7.27/1.48  
% 7.27/1.48  ------ BMC1 Options
% 7.27/1.48  
% 7.27/1.48  --bmc1_incremental                      false
% 7.27/1.48  --bmc1_axioms                           reachable_all
% 7.27/1.48  --bmc1_min_bound                        0
% 7.27/1.48  --bmc1_max_bound                        -1
% 7.27/1.48  --bmc1_max_bound_default                -1
% 7.27/1.48  --bmc1_symbol_reachability              true
% 7.27/1.48  --bmc1_property_lemmas                  false
% 7.27/1.48  --bmc1_k_induction                      false
% 7.27/1.48  --bmc1_non_equiv_states                 false
% 7.27/1.48  --bmc1_deadlock                         false
% 7.27/1.48  --bmc1_ucm                              false
% 7.27/1.48  --bmc1_add_unsat_core                   none
% 7.27/1.48  --bmc1_unsat_core_children              false
% 7.27/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.27/1.48  --bmc1_out_stat                         full
% 7.27/1.48  --bmc1_ground_init                      false
% 7.27/1.48  --bmc1_pre_inst_next_state              false
% 7.27/1.48  --bmc1_pre_inst_state                   false
% 7.27/1.48  --bmc1_pre_inst_reach_state             false
% 7.27/1.48  --bmc1_out_unsat_core                   false
% 7.27/1.48  --bmc1_aig_witness_out                  false
% 7.27/1.48  --bmc1_verbose                          false
% 7.27/1.48  --bmc1_dump_clauses_tptp                false
% 7.27/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.27/1.48  --bmc1_dump_file                        -
% 7.27/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.27/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.27/1.48  --bmc1_ucm_extend_mode                  1
% 7.27/1.48  --bmc1_ucm_init_mode                    2
% 7.27/1.48  --bmc1_ucm_cone_mode                    none
% 7.27/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.27/1.48  --bmc1_ucm_relax_model                  4
% 7.27/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.27/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.27/1.48  --bmc1_ucm_layered_model                none
% 7.27/1.48  --bmc1_ucm_max_lemma_size               10
% 7.27/1.48  
% 7.27/1.48  ------ AIG Options
% 7.27/1.48  
% 7.27/1.48  --aig_mode                              false
% 7.27/1.48  
% 7.27/1.48  ------ Instantiation Options
% 7.27/1.48  
% 7.27/1.48  --instantiation_flag                    true
% 7.27/1.48  --inst_sos_flag                         false
% 7.27/1.48  --inst_sos_phase                        true
% 7.27/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.27/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.27/1.48  --inst_lit_sel_side                     none
% 7.27/1.48  --inst_solver_per_active                1400
% 7.27/1.48  --inst_solver_calls_frac                1.
% 7.27/1.48  --inst_passive_queue_type               priority_queues
% 7.27/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.27/1.48  --inst_passive_queues_freq              [25;2]
% 7.27/1.48  --inst_dismatching                      true
% 7.27/1.48  --inst_eager_unprocessed_to_passive     true
% 7.27/1.48  --inst_prop_sim_given                   true
% 7.27/1.48  --inst_prop_sim_new                     false
% 7.27/1.48  --inst_subs_new                         false
% 7.27/1.48  --inst_eq_res_simp                      false
% 7.27/1.48  --inst_subs_given                       false
% 7.27/1.48  --inst_orphan_elimination               true
% 7.27/1.48  --inst_learning_loop_flag               true
% 7.27/1.48  --inst_learning_start                   3000
% 7.27/1.48  --inst_learning_factor                  2
% 7.27/1.48  --inst_start_prop_sim_after_learn       3
% 7.27/1.48  --inst_sel_renew                        solver
% 7.27/1.48  --inst_lit_activity_flag                true
% 7.27/1.48  --inst_restr_to_given                   false
% 7.27/1.48  --inst_activity_threshold               500
% 7.27/1.48  --inst_out_proof                        true
% 7.27/1.48  
% 7.27/1.48  ------ Resolution Options
% 7.27/1.48  
% 7.27/1.48  --resolution_flag                       false
% 7.27/1.48  --res_lit_sel                           adaptive
% 7.27/1.48  --res_lit_sel_side                      none
% 7.27/1.48  --res_ordering                          kbo
% 7.27/1.48  --res_to_prop_solver                    active
% 7.27/1.48  --res_prop_simpl_new                    false
% 7.27/1.48  --res_prop_simpl_given                  true
% 7.27/1.48  --res_passive_queue_type                priority_queues
% 7.27/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.27/1.48  --res_passive_queues_freq               [15;5]
% 7.27/1.48  --res_forward_subs                      full
% 7.27/1.48  --res_backward_subs                     full
% 7.27/1.48  --res_forward_subs_resolution           true
% 7.27/1.48  --res_backward_subs_resolution          true
% 7.27/1.48  --res_orphan_elimination                true
% 7.27/1.48  --res_time_limit                        2.
% 7.27/1.48  --res_out_proof                         true
% 7.27/1.48  
% 7.27/1.48  ------ Superposition Options
% 7.27/1.48  
% 7.27/1.48  --superposition_flag                    true
% 7.27/1.48  --sup_passive_queue_type                priority_queues
% 7.27/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.27/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.27/1.48  --demod_completeness_check              fast
% 7.27/1.48  --demod_use_ground                      true
% 7.27/1.48  --sup_to_prop_solver                    passive
% 7.27/1.48  --sup_prop_simpl_new                    true
% 7.27/1.48  --sup_prop_simpl_given                  true
% 7.27/1.48  --sup_fun_splitting                     false
% 7.27/1.48  --sup_smt_interval                      50000
% 7.27/1.48  
% 7.27/1.48  ------ Superposition Simplification Setup
% 7.27/1.48  
% 7.27/1.48  --sup_indices_passive                   []
% 7.27/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.27/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_full_bw                           [BwDemod]
% 7.27/1.48  --sup_immed_triv                        [TrivRules]
% 7.27/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_immed_bw_main                     []
% 7.27/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.27/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.27/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.27/1.48  
% 7.27/1.48  ------ Combination Options
% 7.27/1.48  
% 7.27/1.48  --comb_res_mult                         3
% 7.27/1.48  --comb_sup_mult                         2
% 7.27/1.48  --comb_inst_mult                        10
% 7.27/1.48  
% 7.27/1.48  ------ Debug Options
% 7.27/1.48  
% 7.27/1.48  --dbg_backtrace                         false
% 7.27/1.48  --dbg_dump_prop_clauses                 false
% 7.27/1.48  --dbg_dump_prop_clauses_file            -
% 7.27/1.48  --dbg_out_stat                          false
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  ------ Proving...
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  % SZS status Theorem for theBenchmark.p
% 7.27/1.48  
% 7.27/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.27/1.48  
% 7.27/1.48  fof(f15,conjecture,(
% 7.27/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f16,negated_conjecture,(
% 7.27/1.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.27/1.48    inference(negated_conjecture,[],[f15])).
% 7.27/1.48  
% 7.27/1.48  fof(f37,plain,(
% 7.27/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.27/1.48    inference(ennf_transformation,[],[f16])).
% 7.27/1.48  
% 7.27/1.48  fof(f38,plain,(
% 7.27/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.27/1.48    inference(flattening,[],[f37])).
% 7.27/1.48  
% 7.27/1.48  fof(f51,plain,(
% 7.27/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f50,plain,(
% 7.27/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f49,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f48,plain,(
% 7.27/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f47,plain,(
% 7.27/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f46,plain,(
% 7.27/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f52,plain,(
% 7.27/1.48    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 7.27/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f51,f50,f49,f48,f47,f46])).
% 7.27/1.48  
% 7.27/1.48  fof(f82,plain,(
% 7.27/1.48    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f4,axiom,(
% 7.27/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f20,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.27/1.48    inference(ennf_transformation,[],[f4])).
% 7.27/1.48  
% 7.27/1.48  fof(f59,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f20])).
% 7.27/1.48  
% 7.27/1.48  fof(f86,plain,(
% 7.27/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f12,axiom,(
% 7.27/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f31,plain,(
% 7.27/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.27/1.48    inference(ennf_transformation,[],[f12])).
% 7.27/1.48  
% 7.27/1.48  fof(f32,plain,(
% 7.27/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.27/1.48    inference(flattening,[],[f31])).
% 7.27/1.48  
% 7.27/1.48  fof(f70,plain,(
% 7.27/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f32])).
% 7.27/1.48  
% 7.27/1.48  fof(f84,plain,(
% 7.27/1.48    v1_funct_1(sK5)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f89,plain,(
% 7.27/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f87,plain,(
% 7.27/1.48    v1_funct_1(sK6)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f13,axiom,(
% 7.27/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f33,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.27/1.48    inference(ennf_transformation,[],[f13])).
% 7.27/1.48  
% 7.27/1.48  fof(f34,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.27/1.48    inference(flattening,[],[f33])).
% 7.27/1.48  
% 7.27/1.48  fof(f44,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.27/1.48    inference(nnf_transformation,[],[f34])).
% 7.27/1.48  
% 7.27/1.48  fof(f45,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.27/1.48    inference(flattening,[],[f44])).
% 7.27/1.48  
% 7.27/1.48  fof(f72,plain,(
% 7.27/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f45])).
% 7.27/1.48  
% 7.27/1.48  fof(f94,plain,(
% 7.27/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.27/1.48    inference(equality_resolution,[],[f72])).
% 7.27/1.48  
% 7.27/1.48  fof(f14,axiom,(
% 7.27/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f35,plain,(
% 7.27/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.27/1.48    inference(ennf_transformation,[],[f14])).
% 7.27/1.48  
% 7.27/1.48  fof(f36,plain,(
% 7.27/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.27/1.48    inference(flattening,[],[f35])).
% 7.27/1.48  
% 7.27/1.48  fof(f74,plain,(
% 7.27/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f36])).
% 7.27/1.48  
% 7.27/1.48  fof(f75,plain,(
% 7.27/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f36])).
% 7.27/1.48  
% 7.27/1.48  fof(f76,plain,(
% 7.27/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f36])).
% 7.27/1.48  
% 7.27/1.48  fof(f78,plain,(
% 7.27/1.48    ~v1_xboole_0(sK2)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f81,plain,(
% 7.27/1.48    ~v1_xboole_0(sK4)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f88,plain,(
% 7.27/1.48    v1_funct_2(sK6,sK4,sK2)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f79,plain,(
% 7.27/1.48    ~v1_xboole_0(sK3)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f85,plain,(
% 7.27/1.48    v1_funct_2(sK5,sK3,sK2)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f6,axiom,(
% 7.27/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f22,plain,(
% 7.27/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.27/1.48    inference(ennf_transformation,[],[f6])).
% 7.27/1.48  
% 7.27/1.48  fof(f23,plain,(
% 7.27/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.27/1.48    inference(flattening,[],[f22])).
% 7.27/1.48  
% 7.27/1.48  fof(f42,plain,(
% 7.27/1.48    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.27/1.48    inference(nnf_transformation,[],[f23])).
% 7.27/1.48  
% 7.27/1.48  fof(f61,plain,(
% 7.27/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f42])).
% 7.27/1.48  
% 7.27/1.48  fof(f83,plain,(
% 7.27/1.48    r1_subset_1(sK3,sK4)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f1,axiom,(
% 7.27/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f39,plain,(
% 7.27/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.27/1.48    inference(nnf_transformation,[],[f1])).
% 7.27/1.48  
% 7.27/1.48  fof(f53,plain,(
% 7.27/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f39])).
% 7.27/1.48  
% 7.27/1.48  fof(f8,axiom,(
% 7.27/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f25,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.27/1.48    inference(ennf_transformation,[],[f8])).
% 7.27/1.48  
% 7.27/1.48  fof(f64,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f25])).
% 7.27/1.48  
% 7.27/1.48  fof(f2,axiom,(
% 7.27/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f17,plain,(
% 7.27/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.27/1.48    inference(rectify,[],[f2])).
% 7.27/1.48  
% 7.27/1.48  fof(f19,plain,(
% 7.27/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.27/1.48    inference(ennf_transformation,[],[f17])).
% 7.27/1.48  
% 7.27/1.48  fof(f40,plain,(
% 7.27/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f41,plain,(
% 7.27/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.27/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f40])).
% 7.27/1.48  
% 7.27/1.48  fof(f55,plain,(
% 7.27/1.48    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f41])).
% 7.27/1.48  
% 7.27/1.48  fof(f3,axiom,(
% 7.27/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f58,plain,(
% 7.27/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f3])).
% 7.27/1.48  
% 7.27/1.48  fof(f7,axiom,(
% 7.27/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f24,plain,(
% 7.27/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.27/1.48    inference(ennf_transformation,[],[f7])).
% 7.27/1.48  
% 7.27/1.48  fof(f63,plain,(
% 7.27/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f24])).
% 7.27/1.48  
% 7.27/1.48  fof(f5,axiom,(
% 7.27/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f21,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.27/1.48    inference(ennf_transformation,[],[f5])).
% 7.27/1.48  
% 7.27/1.48  fof(f60,plain,(
% 7.27/1.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f21])).
% 7.27/1.48  
% 7.27/1.48  fof(f77,plain,(
% 7.27/1.48    ~v1_xboole_0(sK1)),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f80,plain,(
% 7.27/1.48    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f71,plain,(
% 7.27/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f45])).
% 7.27/1.48  
% 7.27/1.48  fof(f95,plain,(
% 7.27/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.27/1.48    inference(equality_resolution,[],[f71])).
% 7.27/1.48  
% 7.27/1.48  fof(f90,plain,(
% 7.27/1.48    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  cnf(c_32,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 7.27/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1230,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_32]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2038,plain,
% 7.27/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.27/1.48      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1245,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 7.27/1.48      | k9_subset_1(X1_56,X2_56,X0_56) = k3_xboole_0(X2_56,X0_56) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2024,plain,
% 7.27/1.48      ( k9_subset_1(X0_56,X1_56,X2_56) = k3_xboole_0(X1_56,X2_56)
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2630,plain,
% 7.27/1.48      ( k9_subset_1(sK1,X0_56,sK4) = k3_xboole_0(X0_56,sK4) ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2038,c_2024]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_28,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 7.27/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1233,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_28]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2035,plain,
% 7.27/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_17,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.27/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1242,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.27/1.48      | ~ v1_funct_1(X0_56)
% 7.27/1.48      | k2_partfun1(X1_56,X2_56,X0_56,X3_56) = k7_relat_1(X0_56,X3_56) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_17]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2027,plain,
% 7.27/1.48      ( k2_partfun1(X0_56,X1_56,X2_56,X3_56) = k7_relat_1(X2_56,X3_56)
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.27/1.48      | v1_funct_1(X2_56) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3373,plain,
% 7.27/1.48      ( k2_partfun1(sK3,sK2,sK5,X0_56) = k7_relat_1(sK5,X0_56)
% 7.27/1.48      | v1_funct_1(sK5) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2035,c_2027]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_30,negated_conjecture,
% 7.27/1.48      ( v1_funct_1(sK5) ),
% 7.27/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2465,plain,
% 7.27/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.27/1.48      | ~ v1_funct_1(sK5)
% 7.27/1.48      | k2_partfun1(X0_56,X1_56,sK5,X2_56) = k7_relat_1(sK5,X2_56) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_1242]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2658,plain,
% 7.27/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.27/1.48      | ~ v1_funct_1(sK5)
% 7.27/1.48      | k2_partfun1(sK3,sK2,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_2465]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4088,plain,
% 7.27/1.48      ( k2_partfun1(sK3,sK2,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_3373,c_30,c_28,c_2658]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_25,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 7.27/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1236,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_25]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2032,plain,
% 7.27/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3372,plain,
% 7.27/1.48      ( k2_partfun1(sK4,sK2,sK6,X0_56) = k7_relat_1(sK6,X0_56)
% 7.27/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2032,c_2027]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_27,negated_conjecture,
% 7.27/1.48      ( v1_funct_1(sK6) ),
% 7.27/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2460,plain,
% 7.27/1.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.27/1.48      | ~ v1_funct_1(sK6)
% 7.27/1.48      | k2_partfun1(X0_56,X1_56,sK6,X2_56) = k7_relat_1(sK6,X2_56) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_1242]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2653,plain,
% 7.27/1.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 7.27/1.48      | ~ v1_funct_1(sK6)
% 7.27/1.48      | k2_partfun1(sK4,sK2,sK6,X0_56) = k7_relat_1(sK6,X0_56) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_2460]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3702,plain,
% 7.27/1.48      ( k2_partfun1(sK4,sK2,sK6,X0_56) = k7_relat_1(sK6,X0_56) ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_3372,c_27,c_25,c_2653]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_19,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_1(X3)
% 7.27/1.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X1)
% 7.27/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.27/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_23,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_1(X3)
% 7.27/1.48      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_22,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_1(X3)
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_21,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_1(X3)
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_215,plain,
% 7.27/1.48      ( ~ v1_funct_1(X3)
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X1)
% 7.27/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_19,c_23,c_22,c_21]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_216,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_1(X3)
% 7.27/1.48      | v1_xboole_0(X1)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_215]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1223,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 7.27/1.48      | ~ v1_funct_2(X3_56,X4_56,X2_56)
% 7.27/1.48      | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
% 7.27/1.48      | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
% 7.27/1.48      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.27/1.48      | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
% 7.27/1.48      | ~ v1_funct_1(X0_56)
% 7.27/1.48      | ~ v1_funct_1(X3_56)
% 7.27/1.48      | v1_xboole_0(X2_56)
% 7.27/1.48      | v1_xboole_0(X1_56)
% 7.27/1.48      | v1_xboole_0(X4_56)
% 7.27/1.48      | v1_xboole_0(X5_56)
% 7.27/1.48      | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X1_56) = X0_56 ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_216]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2045,plain,
% 7.27/1.48      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X0_56) = X2_56
% 7.27/1.48      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 7.27/1.48      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 7.27/1.48      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.27/1.48      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 7.27/1.48      | v1_funct_1(X2_56) != iProver_top
% 7.27/1.48      | v1_funct_1(X5_56) != iProver_top
% 7.27/1.48      | v1_xboole_0(X3_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X4_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1223]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7923,plain,
% 7.27/1.48      ( k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),sK4) = sK6
% 7.27/1.48      | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
% 7.27/1.48      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(X1_56) != iProver_top
% 7.27/1.48      | v1_funct_1(sK6) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK2) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK4) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_3702,c_2045]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_36,negated_conjecture,
% 7.27/1.48      ( ~ v1_xboole_0(sK2) ),
% 7.27/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_39,plain,
% 7.27/1.48      ( v1_xboole_0(sK2) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_33,negated_conjecture,
% 7.27/1.48      ( ~ v1_xboole_0(sK4) ),
% 7.27/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_42,plain,
% 7.27/1.48      ( v1_xboole_0(sK4) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_48,plain,
% 7.27/1.48      ( v1_funct_1(sK6) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_26,negated_conjecture,
% 7.27/1.48      ( v1_funct_2(sK6,sK4,sK2) ),
% 7.27/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_49,plain,
% 7.27/1.48      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_50,plain,
% 7.27/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18283,plain,
% 7.27/1.48      ( v1_funct_1(X1_56) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
% 7.27/1.48      | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),sK4) = sK6
% 7.27/1.48      | k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_7923,c_39,c_42,c_48,c_49,c_50]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18284,plain,
% 7.27/1.48      ( k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),sK4) = sK6
% 7.27/1.48      | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(X1_56) != iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_18283]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18299,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.27/1.48      | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
% 7.27/1.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(sK5) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_4088,c_18284]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_35,negated_conjecture,
% 7.27/1.48      ( ~ v1_xboole_0(sK3) ),
% 7.27/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_40,plain,
% 7.27/1.48      ( v1_xboole_0(sK3) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_45,plain,
% 7.27/1.48      ( v1_funct_1(sK5) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_29,negated_conjecture,
% 7.27/1.48      ( v1_funct_2(sK5,sK3,sK2) ),
% 7.27/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_46,plain,
% 7.27/1.48      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_47,plain,
% 7.27/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18474,plain,
% 7.27/1.48      ( v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.27/1.48      | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_18299,c_40,c_45,c_46,c_47]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18475,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.27/1.48      | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_18474]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18485,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.27/1.48      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2630,c_18475]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9,plain,
% 7.27/1.48      ( ~ r1_subset_1(X0,X1)
% 7.27/1.48      | r1_xboole_0(X0,X1)
% 7.27/1.48      | v1_xboole_0(X0)
% 7.27/1.48      | v1_xboole_0(X1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_31,negated_conjecture,
% 7.27/1.48      ( r1_subset_1(sK3,sK4) ),
% 7.27/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_565,plain,
% 7.27/1.48      ( r1_xboole_0(X0,X1)
% 7.27/1.48      | v1_xboole_0(X0)
% 7.27/1.48      | v1_xboole_0(X1)
% 7.27/1.48      | sK4 != X1
% 7.27/1.48      | sK3 != X0 ),
% 7.27/1.48      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_566,plain,
% 7.27/1.48      ( r1_xboole_0(sK3,sK4) | v1_xboole_0(sK4) | v1_xboole_0(sK3) ),
% 7.27/1.48      inference(unflattening,[status(thm)],[c_565]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_568,plain,
% 7.27/1.48      ( r1_xboole_0(sK3,sK4) ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_566,c_35,c_33]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1221,plain,
% 7.27/1.48      ( r1_xboole_0(sK3,sK4) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_568]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2047,plain,
% 7.27/1.48      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1221]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1,plain,
% 7.27/1.48      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.27/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1249,plain,
% 7.27/1.48      ( ~ r1_xboole_0(X0_56,X1_56)
% 7.27/1.48      | k3_xboole_0(X0_56,X1_56) = k1_xboole_0 ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2020,plain,
% 7.27/1.48      ( k3_xboole_0(X0_56,X1_56) = k1_xboole_0
% 7.27/1.48      | r1_xboole_0(X0_56,X1_56) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3039,plain,
% 7.27/1.48      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2047,c_2020]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | v1_relat_1(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1243,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.27/1.48      | v1_relat_1(X0_56) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_11]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2026,plain,
% 7.27/1.48      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
% 7.27/1.48      | v1_relat_1(X0_56) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1243]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2975,plain,
% 7.27/1.48      ( v1_relat_1(sK6) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2032,c_2026]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4,plain,
% 7.27/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1246,plain,
% 7.27/1.48      ( r2_hidden(sK0(X0_56,X1_56),X0_56) | r1_xboole_0(X0_56,X1_56) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2023,plain,
% 7.27/1.48      ( r2_hidden(sK0(X0_56,X1_56),X0_56) = iProver_top
% 7.27/1.48      | r1_xboole_0(X0_56,X1_56) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1246]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_5,plain,
% 7.27/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10,plain,
% 7.27/1.48      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_491,plain,
% 7.27/1.48      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.27/1.48      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_492,plain,
% 7.27/1.48      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.27/1.48      inference(unflattening,[status(thm)],[c_491]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1222,plain,
% 7.27/1.48      ( ~ r2_hidden(X0_58,k1_xboole_0) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_492]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2046,plain,
% 7.27/1.48      ( r2_hidden(X0_58,k1_xboole_0) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1222]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3088,plain,
% 7.27/1.48      ( r1_xboole_0(k1_xboole_0,X0_56) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2023,c_2046]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7,plain,
% 7.27/1.48      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.27/1.48      | ~ v1_relat_1(X1)
% 7.27/1.48      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.27/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1244,plain,
% 7.27/1.48      ( ~ r1_xboole_0(X0_56,k1_relat_1(X1_56))
% 7.27/1.48      | ~ v1_relat_1(X1_56)
% 7.27/1.48      | k7_relat_1(X1_56,X0_56) = k1_xboole_0 ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2025,plain,
% 7.27/1.48      ( k7_relat_1(X0_56,X1_56) = k1_xboole_0
% 7.27/1.48      | r1_xboole_0(X1_56,k1_relat_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_relat_1(X0_56) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3392,plain,
% 7.27/1.48      ( k7_relat_1(X0_56,k1_xboole_0) = k1_xboole_0
% 7.27/1.48      | v1_relat_1(X0_56) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_3088,c_2025]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4174,plain,
% 7.27/1.48      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2975,c_3392]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18486,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.27/1.48      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(light_normalisation,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_18485,c_3039,c_4174]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1240,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 7.27/1.48      | ~ v1_funct_2(X3_56,X4_56,X2_56)
% 7.27/1.48      | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
% 7.27/1.48      | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
% 7.27/1.48      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.27/1.48      | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
% 7.27/1.48      | m1_subset_1(k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_56,X4_56,X1_56),X2_56)))
% 7.27/1.48      | ~ v1_funct_1(X0_56)
% 7.27/1.48      | ~ v1_funct_1(X3_56)
% 7.27/1.48      | v1_xboole_0(X2_56)
% 7.27/1.48      | v1_xboole_0(X1_56)
% 7.27/1.48      | v1_xboole_0(X4_56)
% 7.27/1.48      | v1_xboole_0(X5_56) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_21]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2029,plain,
% 7.27/1.48      ( v1_funct_2(X0_56,X1_56,X2_56) != iProver_top
% 7.27/1.48      | v1_funct_2(X3_56,X4_56,X2_56) != iProver_top
% 7.27/1.48      | m1_subset_1(X4_56,k1_zfmisc_1(X5_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(X5_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
% 7.27/1.48      | m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56))) != iProver_top
% 7.27/1.48      | m1_subset_1(k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_56,X4_56,X1_56),X2_56))) = iProver_top
% 7.27/1.48      | v1_funct_1(X0_56) != iProver_top
% 7.27/1.48      | v1_funct_1(X3_56) != iProver_top
% 7.27/1.48      | v1_xboole_0(X5_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X4_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4919,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,X1_56,X2_56),X3_56,k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56),X6_56) = k7_relat_1(k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56),X6_56)
% 7.27/1.48      | v1_funct_2(X5_56,X2_56,X3_56) != iProver_top
% 7.27/1.48      | v1_funct_2(X4_56,X1_56,X3_56) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X2_56,X3_56))) != iProver_top
% 7.27/1.48      | m1_subset_1(X4_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X3_56))) != iProver_top
% 7.27/1.48      | v1_funct_1(X5_56) != iProver_top
% 7.27/1.48      | v1_funct_1(X4_56) != iProver_top
% 7.27/1.48      | v1_funct_1(k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56)) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X3_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2029,c_2027]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1238,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 7.27/1.48      | ~ v1_funct_2(X3_56,X4_56,X2_56)
% 7.27/1.48      | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
% 7.27/1.48      | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
% 7.27/1.48      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.27/1.48      | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
% 7.27/1.48      | ~ v1_funct_1(X0_56)
% 7.27/1.48      | ~ v1_funct_1(X3_56)
% 7.27/1.48      | v1_funct_1(k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56))
% 7.27/1.48      | v1_xboole_0(X2_56)
% 7.27/1.48      | v1_xboole_0(X1_56)
% 7.27/1.48      | v1_xboole_0(X4_56)
% 7.27/1.48      | v1_xboole_0(X5_56) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_23]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2031,plain,
% 7.27/1.48      ( v1_funct_2(X0_56,X1_56,X2_56) != iProver_top
% 7.27/1.48      | v1_funct_2(X3_56,X4_56,X2_56) != iProver_top
% 7.27/1.48      | m1_subset_1(X4_56,k1_zfmisc_1(X5_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(X5_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
% 7.27/1.48      | m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56))) != iProver_top
% 7.27/1.48      | v1_funct_1(X0_56) != iProver_top
% 7.27/1.48      | v1_funct_1(X3_56) != iProver_top
% 7.27/1.48      | v1_funct_1(k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56)) = iProver_top
% 7.27/1.48      | v1_xboole_0(X5_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X4_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8747,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,X1_56,X2_56),X3_56,k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56),X6_56) = k7_relat_1(k1_tmap_1(X0_56,X3_56,X1_56,X2_56,X4_56,X5_56),X6_56)
% 7.27/1.48      | v1_funct_2(X5_56,X2_56,X3_56) != iProver_top
% 7.27/1.48      | v1_funct_2(X4_56,X1_56,X3_56) != iProver_top
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X2_56,X3_56))) != iProver_top
% 7.27/1.48      | m1_subset_1(X4_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X3_56))) != iProver_top
% 7.27/1.48      | v1_funct_1(X5_56) != iProver_top
% 7.27/1.48      | v1_funct_1(X4_56) != iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X3_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(forward_subsumption_resolution,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_4919,c_2031]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8751,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,X1_56,sK4),sK2,k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56)
% 7.27/1.48      | v1_funct_2(X2_56,X1_56,sK2) != iProver_top
% 7.27/1.48      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(X2_56) != iProver_top
% 7.27/1.48      | v1_funct_1(sK6) != iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK2) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK4) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2032,c_8747]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8931,plain,
% 7.27/1.48      ( v1_funct_1(X2_56) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | k2_partfun1(k4_subset_1(X0_56,X1_56,sK4),sK2,k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56)
% 7.27/1.48      | v1_funct_2(X2_56,X1_56,sK2) != iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_8751,c_39,c_42,c_48,c_49]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8932,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,X1_56,sK4),sK2,k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,X1_56,sK4,X2_56,sK6),X3_56)
% 7.27/1.48      | v1_funct_2(X2_56,X1_56,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(X2_56) != iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_8931]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8946,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56)
% 7.27/1.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(sK5) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2035,c_8932]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9910,plain,
% 7.27/1.48      ( v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56)
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_8946,c_40,c_45,c_46]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9911,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56) = k7_relat_1(k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),X1_56)
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_9910]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9920,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0_56) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0_56)
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2038,c_9911]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_37,negated_conjecture,
% 7.27/1.48      ( ~ v1_xboole_0(sK1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_38,plain,
% 7.27/1.48      ( v1_xboole_0(sK1) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_34,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.27/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_41,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9992,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0_56) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0_56) ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_9920,c_38,c_41]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18487,plain,
% 7.27/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.27/1.48      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k1_xboole_0
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_18486,c_2630,c_9992]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2976,plain,
% 7.27/1.48      ( v1_relat_1(sK5) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2035,c_2026]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4175,plain,
% 7.27/1.48      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2976,c_3392]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18488,plain,
% 7.27/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.27/1.48      | k1_xboole_0 != k1_xboole_0
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(light_normalisation,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_18487,c_3039,c_4175]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18489,plain,
% 7.27/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(equality_resolution_simp,[status(thm)],[c_18488]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_20,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_1(X3)
% 7.27/1.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X1)
% 7.27/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.27/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_208,plain,
% 7.27/1.48      ( ~ v1_funct_1(X3)
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X1)
% 7.27/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_20,c_23,c_22,c_21]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_209,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.27/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | ~ v1_funct_1(X3)
% 7.27/1.48      | v1_xboole_0(X1)
% 7.27/1.48      | v1_xboole_0(X2)
% 7.27/1.48      | v1_xboole_0(X4)
% 7.27/1.48      | v1_xboole_0(X5)
% 7.27/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_208]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1224,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 7.27/1.48      | ~ v1_funct_2(X3_56,X4_56,X2_56)
% 7.27/1.48      | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
% 7.27/1.48      | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
% 7.27/1.48      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.27/1.48      | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
% 7.27/1.48      | ~ v1_funct_1(X0_56)
% 7.27/1.48      | ~ v1_funct_1(X3_56)
% 7.27/1.48      | v1_xboole_0(X2_56)
% 7.27/1.48      | v1_xboole_0(X1_56)
% 7.27/1.48      | v1_xboole_0(X4_56)
% 7.27/1.48      | v1_xboole_0(X5_56)
% 7.27/1.48      | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X4_56) = X3_56 ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_209]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2044,plain,
% 7.27/1.48      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X4_56) = X5_56
% 7.27/1.48      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 7.27/1.48      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 7.27/1.48      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.27/1.48      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 7.27/1.48      | v1_funct_1(X2_56) != iProver_top
% 7.27/1.48      | v1_funct_1(X5_56) != iProver_top
% 7.27/1.48      | v1_xboole_0(X3_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X1_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X4_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_1224]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_5869,plain,
% 7.27/1.48      ( k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),X0_56) = X1_56
% 7.27/1.48      | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
% 7.27/1.48      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(X1_56) != iProver_top
% 7.27/1.48      | v1_funct_1(sK6) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK2) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK4) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_3702,c_2044]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11253,plain,
% 7.27/1.48      ( v1_funct_1(X1_56) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
% 7.27/1.48      | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),X0_56) = X1_56
% 7.27/1.48      | k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_5869,c_39,c_42,c_48,c_49,c_50]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11254,plain,
% 7.27/1.48      ( k2_partfun1(X0_56,sK2,X1_56,k9_subset_1(X2_56,X0_56,sK4)) != k7_relat_1(sK6,k9_subset_1(X2_56,X0_56,sK4))
% 7.27/1.48      | k2_partfun1(k4_subset_1(X2_56,X0_56,sK4),sK2,k1_tmap_1(X2_56,sK2,X0_56,sK4,X1_56,sK6),X0_56) = X1_56
% 7.27/1.48      | v1_funct_2(X1_56,X0_56,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X2_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(X1_56) != iProver_top
% 7.27/1.48      | v1_xboole_0(X2_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_11253]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11269,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.27/1.48      | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
% 7.27/1.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.27/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_funct_1(sK5) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_4088,c_11254]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11553,plain,
% 7.27/1.48      ( v1_xboole_0(X0_56) = iProver_top
% 7.27/1.48      | k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.27/1.48      | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_11269,c_40,c_45,c_46,c_47]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11554,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(X0_56,sK3,sK4),sK2,k1_tmap_1(X0_56,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.27/1.48      | k7_relat_1(sK6,k9_subset_1(X0_56,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK3,sK4))
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.27/1.48      | v1_xboole_0(X0_56) = iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_11553]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11564,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.27/1.48      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2630,c_11554]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11565,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.27/1.48      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(light_normalisation,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_11564,c_3039,c_4174]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11566,plain,
% 7.27/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.27/1.48      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k1_xboole_0
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_11565,c_2630,c_9992]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11567,plain,
% 7.27/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.27/1.48      | k1_xboole_0 != k1_xboole_0
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(light_normalisation,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_11566,c_3039,c_4175]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11568,plain,
% 7.27/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.27/1.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.27/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.27/1.48      inference(equality_resolution_simp,[status(thm)],[c_11567]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24,negated_conjecture,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 7.27/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_1237,negated_conjecture,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 7.27/1.48      inference(subtyping,[status(esa)],[c_24]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2817,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k2_partfun1(sK4,sK2,sK6,k3_xboole_0(sK3,sK4)) != k2_partfun1(sK3,sK2,sK5,k3_xboole_0(sK3,sK4)) ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_2630,c_1237]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3230,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_3039,c_2817]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3706,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_3702,c_3230]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4092,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_3706,c_4088]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4181,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_4174,c_4092]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2377,plain,
% 7.27/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.27/1.48      | v1_relat_1(sK5) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_1243]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2544,plain,
% 7.27/1.48      ( r2_hidden(sK0(k1_xboole_0,X0_56),k1_xboole_0)
% 7.27/1.48      | r1_xboole_0(k1_xboole_0,X0_56) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_1246]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2892,plain,
% 7.27/1.48      ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK5)),k1_xboole_0)
% 7.27/1.48      | r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_2544]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2585,plain,
% 7.27/1.48      ( ~ r1_xboole_0(X0_56,k1_relat_1(sK5))
% 7.27/1.48      | ~ v1_relat_1(sK5)
% 7.27/1.48      | k7_relat_1(sK5,X0_56) = k1_xboole_0 ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_1244]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2893,plain,
% 7.27/1.48      ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
% 7.27/1.48      | ~ v1_relat_1(sK5)
% 7.27/1.48      | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_2585]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2545,plain,
% 7.27/1.48      ( ~ r2_hidden(sK0(k1_xboole_0,X0_56),k1_xboole_0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_1222]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3358,plain,
% 7.27/1.48      ( ~ r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK5)),k1_xboole_0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_2545]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4240,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_4181,c_28,c_2377,c_2892,c_2893,c_3358]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4241,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_4240]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9996,plain,
% 7.27/1.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.27/1.48      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_9992,c_4241]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9997,plain,
% 7.27/1.48      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.27/1.48      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_9996,c_9992]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_43,plain,
% 7.27/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(contradiction,plain,
% 7.27/1.48      ( $false ),
% 7.27/1.48      inference(minisat,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_18489,c_11568,c_9997,c_43,c_41,c_38]) ).
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.27/1.48  
% 7.27/1.48  ------                               Statistics
% 7.27/1.48  
% 7.27/1.48  ------ General
% 7.27/1.48  
% 7.27/1.48  abstr_ref_over_cycles:                  0
% 7.27/1.48  abstr_ref_under_cycles:                 0
% 7.27/1.48  gc_basic_clause_elim:                   0
% 7.27/1.48  forced_gc_time:                         0
% 7.27/1.48  parsing_time:                           0.011
% 7.27/1.48  unif_index_cands_time:                  0.
% 7.27/1.48  unif_index_add_time:                    0.
% 7.27/1.48  orderings_time:                         0.
% 7.27/1.48  out_proof_time:                         0.017
% 7.27/1.48  total_time:                             0.928
% 7.27/1.48  num_of_symbols:                         62
% 7.27/1.48  num_of_terms:                           33904
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing
% 7.27/1.48  
% 7.27/1.48  num_of_splits:                          0
% 7.27/1.48  num_of_split_atoms:                     0
% 7.27/1.48  num_of_reused_defs:                     0
% 7.27/1.48  num_eq_ax_congr_red:                    29
% 7.27/1.48  num_of_sem_filtered_clauses:            1
% 7.27/1.48  num_of_subtypes:                        3
% 7.27/1.48  monotx_restored_types:                  0
% 7.27/1.48  sat_num_of_epr_types:                   0
% 7.27/1.48  sat_num_of_non_cyclic_types:            0
% 7.27/1.48  sat_guarded_non_collapsed_types:        1
% 7.27/1.48  num_pure_diseq_elim:                    0
% 7.27/1.48  simp_replaced_by:                       0
% 7.27/1.48  res_preprocessed:                       163
% 7.27/1.48  prep_upred:                             0
% 7.27/1.48  prep_unflattend:                        44
% 7.27/1.48  smt_new_axioms:                         0
% 7.27/1.48  pred_elim_cands:                        7
% 7.27/1.48  pred_elim:                              4
% 7.27/1.48  pred_elim_cl:                           6
% 7.27/1.48  pred_elim_cycles:                       8
% 7.27/1.48  merged_defs:                            8
% 7.27/1.48  merged_defs_ncl:                        0
% 7.27/1.48  bin_hyper_res:                          8
% 7.27/1.48  prep_cycles:                            4
% 7.27/1.48  pred_elim_time:                         0.008
% 7.27/1.48  splitting_time:                         0.
% 7.27/1.48  sem_filter_time:                        0.
% 7.27/1.48  monotx_time:                            0.
% 7.27/1.48  subtype_inf_time:                       0.001
% 7.27/1.48  
% 7.27/1.48  ------ Problem properties
% 7.27/1.48  
% 7.27/1.48  clauses:                                31
% 7.27/1.48  conjectures:                            13
% 7.27/1.48  epr:                                    11
% 7.27/1.48  horn:                                   22
% 7.27/1.48  ground:                                 14
% 7.27/1.48  unary:                                  14
% 7.27/1.48  binary:                                 6
% 7.27/1.48  lits:                                   127
% 7.27/1.48  lits_eq:                                15
% 7.27/1.48  fd_pure:                                0
% 7.27/1.48  fd_pseudo:                              0
% 7.27/1.48  fd_cond:                                0
% 7.27/1.48  fd_pseudo_cond:                         1
% 7.27/1.48  ac_symbols:                             0
% 7.27/1.48  
% 7.27/1.48  ------ Propositional Solver
% 7.27/1.48  
% 7.27/1.48  prop_solver_calls:                      30
% 7.27/1.48  prop_fast_solver_calls:                 2896
% 7.27/1.48  smt_solver_calls:                       0
% 7.27/1.48  smt_fast_solver_calls:                  0
% 7.27/1.48  prop_num_of_clauses:                    7006
% 7.27/1.48  prop_preprocess_simplified:             16503
% 7.27/1.48  prop_fo_subsumed:                       203
% 7.27/1.48  prop_solver_time:                       0.
% 7.27/1.48  smt_solver_time:                        0.
% 7.27/1.48  smt_fast_solver_time:                   0.
% 7.27/1.48  prop_fast_solver_time:                  0.
% 7.27/1.48  prop_unsat_core_time:                   0.
% 7.27/1.48  
% 7.27/1.48  ------ QBF
% 7.27/1.48  
% 7.27/1.48  qbf_q_res:                              0
% 7.27/1.48  qbf_num_tautologies:                    0
% 7.27/1.48  qbf_prep_cycles:                        0
% 7.27/1.48  
% 7.27/1.48  ------ BMC1
% 7.27/1.48  
% 7.27/1.48  bmc1_current_bound:                     -1
% 7.27/1.48  bmc1_last_solved_bound:                 -1
% 7.27/1.48  bmc1_unsat_core_size:                   -1
% 7.27/1.48  bmc1_unsat_core_parents_size:           -1
% 7.27/1.48  bmc1_merge_next_fun:                    0
% 7.27/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.27/1.48  
% 7.27/1.48  ------ Instantiation
% 7.27/1.48  
% 7.27/1.48  inst_num_of_clauses:                    1695
% 7.27/1.48  inst_num_in_passive:                    884
% 7.27/1.48  inst_num_in_active:                     714
% 7.27/1.48  inst_num_in_unprocessed:                97
% 7.27/1.48  inst_num_of_loops:                      730
% 7.27/1.48  inst_num_of_learning_restarts:          0
% 7.27/1.48  inst_num_moves_active_passive:          12
% 7.27/1.48  inst_lit_activity:                      0
% 7.27/1.48  inst_lit_activity_moves:                0
% 7.27/1.48  inst_num_tautologies:                   0
% 7.27/1.48  inst_num_prop_implied:                  0
% 7.27/1.48  inst_num_existing_simplified:           0
% 7.27/1.48  inst_num_eq_res_simplified:             0
% 7.27/1.48  inst_num_child_elim:                    0
% 7.27/1.48  inst_num_of_dismatching_blockings:      198
% 7.27/1.48  inst_num_of_non_proper_insts:           1369
% 7.27/1.48  inst_num_of_duplicates:                 0
% 7.27/1.48  inst_inst_num_from_inst_to_res:         0
% 7.27/1.48  inst_dismatching_checking_time:         0.
% 7.27/1.48  
% 7.27/1.48  ------ Resolution
% 7.27/1.48  
% 7.27/1.48  res_num_of_clauses:                     0
% 7.27/1.48  res_num_in_passive:                     0
% 7.27/1.48  res_num_in_active:                      0
% 7.27/1.48  res_num_of_loops:                       167
% 7.27/1.48  res_forward_subset_subsumed:            70
% 7.27/1.48  res_backward_subset_subsumed:           4
% 7.27/1.48  res_forward_subsumed:                   0
% 7.27/1.48  res_backward_subsumed:                  0
% 7.27/1.48  res_forward_subsumption_resolution:     1
% 7.27/1.48  res_backward_subsumption_resolution:    0
% 7.27/1.48  res_clause_to_clause_subsumption:       1732
% 7.27/1.48  res_orphan_elimination:                 0
% 7.27/1.48  res_tautology_del:                      56
% 7.27/1.48  res_num_eq_res_simplified:              0
% 7.27/1.48  res_num_sel_changes:                    0
% 7.27/1.48  res_moves_from_active_to_pass:          0
% 7.27/1.48  
% 7.27/1.48  ------ Superposition
% 7.27/1.48  
% 7.27/1.48  sup_time_total:                         0.
% 7.27/1.48  sup_time_generating:                    0.
% 7.27/1.48  sup_time_sim_full:                      0.
% 7.27/1.48  sup_time_sim_immed:                     0.
% 7.27/1.48  
% 7.27/1.48  sup_num_of_clauses:                     262
% 7.27/1.48  sup_num_in_active:                      139
% 7.27/1.48  sup_num_in_passive:                     123
% 7.27/1.48  sup_num_of_loops:                       144
% 7.27/1.48  sup_fw_superposition:                   216
% 7.27/1.48  sup_bw_superposition:                   65
% 7.27/1.48  sup_immediate_simplified:               121
% 7.27/1.48  sup_given_eliminated:                   0
% 7.27/1.48  comparisons_done:                       0
% 7.27/1.48  comparisons_avoided:                    0
% 7.27/1.48  
% 7.27/1.48  ------ Simplifications
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  sim_fw_subset_subsumed:                 0
% 7.27/1.48  sim_bw_subset_subsumed:                 2
% 7.27/1.48  sim_fw_subsumed:                        6
% 7.27/1.48  sim_bw_subsumed:                        8
% 7.27/1.48  sim_fw_subsumption_res:                 3
% 7.27/1.48  sim_bw_subsumption_res:                 0
% 7.27/1.48  sim_tautology_del:                      1
% 7.27/1.48  sim_eq_tautology_del:                   5
% 7.27/1.48  sim_eq_res_simp:                        5
% 7.27/1.48  sim_fw_demodulated:                     73
% 7.27/1.48  sim_bw_demodulated:                     6
% 7.27/1.48  sim_light_normalised:                   55
% 7.27/1.48  sim_joinable_taut:                      0
% 7.27/1.48  sim_joinable_simp:                      0
% 7.27/1.48  sim_ac_normalised:                      0
% 7.27/1.48  sim_smt_subsumption:                    0
% 7.27/1.48  
%------------------------------------------------------------------------------
