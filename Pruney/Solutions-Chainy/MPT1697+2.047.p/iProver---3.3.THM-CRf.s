%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:32 EST 2020

% Result     : Theorem 7.33s
% Output     : CNFRefutation 7.33s
% Verified   : 
% Statistics : Number of formulae       :  202 (1957 expanded)
%              Number of clauses        :  125 ( 531 expanded)
%              Number of leaves         :   19 ( 715 expanded)
%              Depth                    :   25
%              Number of atoms          : 1094 (22347 expanded)
%              Number of equality atoms :  402 (5300 expanded)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f38,f55,f54,f53,f52,f51,f50])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f56])).

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
    inference(nnf_transformation,[],[f34])).

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

fof(f77,plain,(
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

fof(f105,plain,(
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
    inference(equality_resolution,[],[f77])).

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

fof(f80,plain,(
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

fof(f81,plain,(
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

fof(f82,plain,(
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

fof(f84,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f83,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(rectify,[],[f3])).

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

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f56])).

fof(f78,plain,(
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

fof(f104,plain,(
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
    inference(equality_resolution,[],[f78])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1227,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_2053,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1242,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2039,plain,
    ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_3184,plain,
    ( k9_subset_1(sK2,X0_57,sK5) = k1_setfam_1(k2_tarski(X0_57,sK5)) ),
    inference(superposition,[status(thm)],[c_2053,c_2039])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1230,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2050,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1239,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2042,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1239])).

cnf(c_3981,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_2042])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_46,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4103,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3981,c_46])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1233,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2047,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_3980,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2047,c_2042])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_49,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4098,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3980,c_49])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f82])).

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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_24,c_23,c_22])).

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

cnf(c_1221,plain,
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
    inference(subtyping,[status(esa)],[c_209])).

cnf(c_2059,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1221])).

cnf(c_4682,plain,
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
    inference(superposition,[status(thm)],[c_4098,c_2059])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_43,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_50,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_51,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4937,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
    | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4682,c_40,c_43,c_49,c_50,c_51])).

cnf(c_4938,plain,
    ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_4937])).

cnf(c_4944,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4103,c_4938])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_41,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_47,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_48,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5045,plain,
    ( v1_xboole_0(X0_57) = iProver_top
    | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4944,c_41,c_46,c_47,c_48])).

cnf(c_5046,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_5045])).

cnf(c_5051,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3184,c_5046])).

cnf(c_11,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_556,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_557,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_559,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_36,c_34])).

cnf(c_1219,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_559])).

cnf(c_2061,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1219])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1247,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2035,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_3092,plain,
    ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2061,c_2035])).

cnf(c_5052,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5051,c_3092])).

cnf(c_5053,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5052,c_3184])).

cnf(c_5054,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5053,c_3092])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5055,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5054])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1240,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2041,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_3259,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2047,c_2041])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1244,plain,
    ( r1_xboole_0(X0_57,X1_57)
    | r2_hidden(sK1(X0_57,X1_57),X0_57) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2038,plain,
    ( r1_xboole_0(X0_57,X1_57) = iProver_top
    | r2_hidden(sK1(X0_57,X1_57),X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_7,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1243,plain,
    ( k1_setfam_1(k2_tarski(X0_57,k1_xboole_0)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1248,plain,
    ( r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2034,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) != k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1248])).

cnf(c_3002,plain,
    ( r1_xboole_0(X0_57,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_2034])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1246,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | ~ r2_hidden(X0_60,X0_57)
    | ~ r2_hidden(X0_60,X1_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2036,plain,
    ( r1_xboole_0(X0_57,X1_57) != iProver_top
    | r2_hidden(X0_60,X1_57) != iProver_top
    | r2_hidden(X0_60,X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_4000,plain,
    ( r2_hidden(X0_60,X0_57) != iProver_top
    | r2_hidden(X0_60,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3002,c_2036])).

cnf(c_4818,plain,
    ( r1_xboole_0(X0_57,X1_57) = iProver_top
    | r2_hidden(sK1(X0_57,X1_57),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_4000])).

cnf(c_5818,plain,
    ( r1_xboole_0(k1_xboole_0,X0_57) = iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_4818])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1241,plain,
    ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2040,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_5855,plain,
    ( k7_relat_1(X0_57,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_5818,c_2040])).

cnf(c_5860,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3259,c_5855])).

cnf(c_25,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1234,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3866,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(demodulation,[status(thm)],[c_3184,c_1234])).

cnf(c_3867,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3866,c_3092])).

cnf(c_4101,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4098,c_3867])).

cnf(c_4125,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4101,c_4103])).

cnf(c_5910,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5860,c_4125])).

cnf(c_3260,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_2041])).

cnf(c_5861,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3260,c_5855])).

cnf(c_5911,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5910,c_5861])).

cnf(c_5912,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_5911])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f104])).

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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_24,c_23,c_22])).

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

cnf(c_1220,plain,
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
    inference(subtyping,[status(esa)],[c_216])).

cnf(c_2060,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1220])).

cnf(c_5774,plain,
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
    inference(superposition,[status(thm)],[c_4098,c_2060])).

cnf(c_7279,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
    | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5774,c_40,c_43,c_49,c_50,c_51])).

cnf(c_7280,plain,
    ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_7279])).

cnf(c_7286,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4103,c_7280])).

cnf(c_7296,plain,
    ( v1_xboole_0(X0_57) = iProver_top
    | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7286,c_41,c_46,c_47,c_48])).

cnf(c_7297,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_7296])).

cnf(c_7302,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3184,c_7297])).

cnf(c_7303,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7302,c_3092,c_5860])).

cnf(c_7304,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7303,c_3184])).

cnf(c_7305,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7304,c_3092,c_5861])).

cnf(c_7306,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7305])).

cnf(c_13786,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5054,c_38,c_39,c_35,c_42,c_33,c_44,c_5055,c_5912,c_7306])).

cnf(c_13788,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13786,c_5860,c_5861])).

cnf(c_13789,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_13788])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.33/1.44  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.33/1.44  
% 7.33/1.44  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.33/1.44  
% 7.33/1.44  ------  iProver source info
% 7.33/1.44  
% 7.33/1.44  git: date: 2020-06-30 10:37:57 +0100
% 7.33/1.44  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.33/1.44  git: non_committed_changes: false
% 7.33/1.44  git: last_make_outside_of_git: false
% 7.33/1.44  
% 7.33/1.44  ------ 
% 7.33/1.44  
% 7.33/1.44  ------ Input Options
% 7.33/1.44  
% 7.33/1.44  --out_options                           all
% 7.33/1.44  --tptp_safe_out                         true
% 7.33/1.44  --problem_path                          ""
% 7.33/1.44  --include_path                          ""
% 7.33/1.44  --clausifier                            res/vclausify_rel
% 7.33/1.44  --clausifier_options                    ""
% 7.33/1.44  --stdin                                 false
% 7.33/1.44  --stats_out                             all
% 7.33/1.44  
% 7.33/1.44  ------ General Options
% 7.33/1.44  
% 7.33/1.44  --fof                                   false
% 7.33/1.44  --time_out_real                         305.
% 7.33/1.44  --time_out_virtual                      -1.
% 7.33/1.44  --symbol_type_check                     false
% 7.33/1.44  --clausify_out                          false
% 7.33/1.44  --sig_cnt_out                           false
% 7.33/1.44  --trig_cnt_out                          false
% 7.33/1.44  --trig_cnt_out_tolerance                1.
% 7.33/1.44  --trig_cnt_out_sk_spl                   false
% 7.33/1.44  --abstr_cl_out                          false
% 7.33/1.44  
% 7.33/1.44  ------ Global Options
% 7.33/1.44  
% 7.33/1.44  --schedule                              default
% 7.33/1.44  --add_important_lit                     false
% 7.33/1.44  --prop_solver_per_cl                    1000
% 7.33/1.44  --min_unsat_core                        false
% 7.33/1.44  --soft_assumptions                      false
% 7.33/1.44  --soft_lemma_size                       3
% 7.33/1.44  --prop_impl_unit_size                   0
% 7.33/1.44  --prop_impl_unit                        []
% 7.33/1.44  --share_sel_clauses                     true
% 7.33/1.44  --reset_solvers                         false
% 7.33/1.44  --bc_imp_inh                            [conj_cone]
% 7.33/1.44  --conj_cone_tolerance                   3.
% 7.33/1.44  --extra_neg_conj                        none
% 7.33/1.44  --large_theory_mode                     true
% 7.33/1.44  --prolific_symb_bound                   200
% 7.33/1.44  --lt_threshold                          2000
% 7.33/1.44  --clause_weak_htbl                      true
% 7.33/1.44  --gc_record_bc_elim                     false
% 7.33/1.44  
% 7.33/1.44  ------ Preprocessing Options
% 7.33/1.44  
% 7.33/1.44  --preprocessing_flag                    true
% 7.33/1.44  --time_out_prep_mult                    0.1
% 7.33/1.44  --splitting_mode                        input
% 7.33/1.44  --splitting_grd                         true
% 7.33/1.44  --splitting_cvd                         false
% 7.33/1.44  --splitting_cvd_svl                     false
% 7.33/1.44  --splitting_nvd                         32
% 7.33/1.44  --sub_typing                            true
% 7.33/1.44  --prep_gs_sim                           true
% 7.33/1.44  --prep_unflatten                        true
% 7.33/1.44  --prep_res_sim                          true
% 7.33/1.44  --prep_upred                            true
% 7.33/1.44  --prep_sem_filter                       exhaustive
% 7.33/1.44  --prep_sem_filter_out                   false
% 7.33/1.44  --pred_elim                             true
% 7.33/1.44  --res_sim_input                         true
% 7.33/1.44  --eq_ax_congr_red                       true
% 7.33/1.44  --pure_diseq_elim                       true
% 7.33/1.44  --brand_transform                       false
% 7.33/1.44  --non_eq_to_eq                          false
% 7.33/1.44  --prep_def_merge                        true
% 7.33/1.44  --prep_def_merge_prop_impl              false
% 7.33/1.44  --prep_def_merge_mbd                    true
% 7.33/1.44  --prep_def_merge_tr_red                 false
% 7.33/1.44  --prep_def_merge_tr_cl                  false
% 7.33/1.44  --smt_preprocessing                     true
% 7.33/1.44  --smt_ac_axioms                         fast
% 7.33/1.44  --preprocessed_out                      false
% 7.33/1.44  --preprocessed_stats                    false
% 7.33/1.44  
% 7.33/1.44  ------ Abstraction refinement Options
% 7.33/1.44  
% 7.33/1.44  --abstr_ref                             []
% 7.33/1.44  --abstr_ref_prep                        false
% 7.33/1.44  --abstr_ref_until_sat                   false
% 7.33/1.44  --abstr_ref_sig_restrict                funpre
% 7.33/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.44  --abstr_ref_under                       []
% 7.33/1.44  
% 7.33/1.44  ------ SAT Options
% 7.33/1.44  
% 7.33/1.44  --sat_mode                              false
% 7.33/1.44  --sat_fm_restart_options                ""
% 7.33/1.44  --sat_gr_def                            false
% 7.33/1.44  --sat_epr_types                         true
% 7.33/1.44  --sat_non_cyclic_types                  false
% 7.33/1.44  --sat_finite_models                     false
% 7.33/1.44  --sat_fm_lemmas                         false
% 7.33/1.44  --sat_fm_prep                           false
% 7.33/1.44  --sat_fm_uc_incr                        true
% 7.33/1.44  --sat_out_model                         small
% 7.33/1.44  --sat_out_clauses                       false
% 7.33/1.44  
% 7.33/1.44  ------ QBF Options
% 7.33/1.44  
% 7.33/1.44  --qbf_mode                              false
% 7.33/1.44  --qbf_elim_univ                         false
% 7.33/1.44  --qbf_dom_inst                          none
% 7.33/1.44  --qbf_dom_pre_inst                      false
% 7.33/1.44  --qbf_sk_in                             false
% 7.33/1.44  --qbf_pred_elim                         true
% 7.33/1.44  --qbf_split                             512
% 7.33/1.44  
% 7.33/1.44  ------ BMC1 Options
% 7.33/1.44  
% 7.33/1.44  --bmc1_incremental                      false
% 7.33/1.44  --bmc1_axioms                           reachable_all
% 7.33/1.44  --bmc1_min_bound                        0
% 7.33/1.44  --bmc1_max_bound                        -1
% 7.33/1.44  --bmc1_max_bound_default                -1
% 7.33/1.44  --bmc1_symbol_reachability              true
% 7.33/1.44  --bmc1_property_lemmas                  false
% 7.33/1.44  --bmc1_k_induction                      false
% 7.33/1.44  --bmc1_non_equiv_states                 false
% 7.33/1.44  --bmc1_deadlock                         false
% 7.33/1.44  --bmc1_ucm                              false
% 7.33/1.44  --bmc1_add_unsat_core                   none
% 7.33/1.44  --bmc1_unsat_core_children              false
% 7.33/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.33/1.44  --bmc1_out_stat                         full
% 7.33/1.44  --bmc1_ground_init                      false
% 7.33/1.44  --bmc1_pre_inst_next_state              false
% 7.33/1.44  --bmc1_pre_inst_state                   false
% 7.33/1.44  --bmc1_pre_inst_reach_state             false
% 7.33/1.44  --bmc1_out_unsat_core                   false
% 7.33/1.44  --bmc1_aig_witness_out                  false
% 7.33/1.44  --bmc1_verbose                          false
% 7.33/1.44  --bmc1_dump_clauses_tptp                false
% 7.33/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.33/1.44  --bmc1_dump_file                        -
% 7.33/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.33/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.33/1.44  --bmc1_ucm_extend_mode                  1
% 7.33/1.44  --bmc1_ucm_init_mode                    2
% 7.33/1.44  --bmc1_ucm_cone_mode                    none
% 7.33/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.33/1.44  --bmc1_ucm_relax_model                  4
% 7.33/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.33/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.33/1.44  --bmc1_ucm_layered_model                none
% 7.33/1.44  --bmc1_ucm_max_lemma_size               10
% 7.33/1.44  
% 7.33/1.44  ------ AIG Options
% 7.33/1.44  
% 7.33/1.44  --aig_mode                              false
% 7.33/1.44  
% 7.33/1.44  ------ Instantiation Options
% 7.33/1.44  
% 7.33/1.44  --instantiation_flag                    true
% 7.33/1.44  --inst_sos_flag                         true
% 7.33/1.44  --inst_sos_phase                        true
% 7.33/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.33/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.33/1.44  --inst_lit_sel_side                     num_symb
% 7.33/1.44  --inst_solver_per_active                1400
% 7.33/1.44  --inst_solver_calls_frac                1.
% 7.33/1.44  --inst_passive_queue_type               priority_queues
% 7.33/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.33/1.44  --inst_passive_queues_freq              [25;2]
% 7.33/1.44  --inst_dismatching                      true
% 7.33/1.44  --inst_eager_unprocessed_to_passive     true
% 7.33/1.44  --inst_prop_sim_given                   true
% 7.33/1.44  --inst_prop_sim_new                     false
% 7.33/1.44  --inst_subs_new                         false
% 7.33/1.44  --inst_eq_res_simp                      false
% 7.33/1.44  --inst_subs_given                       false
% 7.33/1.44  --inst_orphan_elimination               true
% 7.33/1.44  --inst_learning_loop_flag               true
% 7.33/1.44  --inst_learning_start                   3000
% 7.33/1.44  --inst_learning_factor                  2
% 7.33/1.44  --inst_start_prop_sim_after_learn       3
% 7.33/1.44  --inst_sel_renew                        solver
% 7.33/1.44  --inst_lit_activity_flag                true
% 7.33/1.44  --inst_restr_to_given                   false
% 7.33/1.44  --inst_activity_threshold               500
% 7.33/1.44  --inst_out_proof                        true
% 7.33/1.44  
% 7.33/1.44  ------ Resolution Options
% 7.33/1.44  
% 7.33/1.44  --resolution_flag                       true
% 7.33/1.44  --res_lit_sel                           adaptive
% 7.33/1.44  --res_lit_sel_side                      none
% 7.33/1.44  --res_ordering                          kbo
% 7.33/1.44  --res_to_prop_solver                    active
% 7.33/1.44  --res_prop_simpl_new                    false
% 7.33/1.44  --res_prop_simpl_given                  true
% 7.33/1.44  --res_passive_queue_type                priority_queues
% 7.33/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.33/1.44  --res_passive_queues_freq               [15;5]
% 7.33/1.44  --res_forward_subs                      full
% 7.33/1.44  --res_backward_subs                     full
% 7.33/1.44  --res_forward_subs_resolution           true
% 7.33/1.44  --res_backward_subs_resolution          true
% 7.33/1.44  --res_orphan_elimination                true
% 7.33/1.44  --res_time_limit                        2.
% 7.33/1.44  --res_out_proof                         true
% 7.33/1.44  
% 7.33/1.44  ------ Superposition Options
% 7.33/1.44  
% 7.33/1.44  --superposition_flag                    true
% 7.33/1.44  --sup_passive_queue_type                priority_queues
% 7.33/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.33/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.33/1.44  --demod_completeness_check              fast
% 7.33/1.44  --demod_use_ground                      true
% 7.33/1.44  --sup_to_prop_solver                    passive
% 7.33/1.44  --sup_prop_simpl_new                    true
% 7.33/1.44  --sup_prop_simpl_given                  true
% 7.33/1.44  --sup_fun_splitting                     true
% 7.33/1.44  --sup_smt_interval                      50000
% 7.33/1.44  
% 7.33/1.44  ------ Superposition Simplification Setup
% 7.33/1.44  
% 7.33/1.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.33/1.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.33/1.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.33/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.33/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.33/1.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.33/1.44  --sup_immed_triv                        [TrivRules]
% 7.33/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.44  --sup_immed_bw_main                     []
% 7.33/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.33/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.33/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.44  --sup_input_bw                          []
% 7.33/1.44  
% 7.33/1.44  ------ Combination Options
% 7.33/1.44  
% 7.33/1.44  --comb_res_mult                         3
% 7.33/1.44  --comb_sup_mult                         2
% 7.33/1.44  --comb_inst_mult                        10
% 7.33/1.44  
% 7.33/1.44  ------ Debug Options
% 7.33/1.44  
% 7.33/1.44  --dbg_backtrace                         false
% 7.33/1.44  --dbg_dump_prop_clauses                 false
% 7.33/1.44  --dbg_dump_prop_clauses_file            -
% 7.33/1.44  --dbg_out_stat                          false
% 7.33/1.44  ------ Parsing...
% 7.33/1.44  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.33/1.44  
% 7.33/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.33/1.44  
% 7.33/1.44  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.33/1.44  
% 7.33/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.33/1.44  ------ Proving...
% 7.33/1.44  ------ Problem Properties 
% 7.33/1.44  
% 7.33/1.44  
% 7.33/1.44  clauses                                 33
% 7.33/1.44  conjectures                             13
% 7.33/1.44  EPR                                     11
% 7.33/1.44  Horn                                    23
% 7.33/1.44  unary                                   14
% 7.33/1.44  binary                                  8
% 7.33/1.44  lits                                    131
% 7.33/1.44  lits eq                                 16
% 7.33/1.44  fd_pure                                 0
% 7.33/1.44  fd_pseudo                               0
% 7.33/1.44  fd_cond                                 0
% 7.33/1.44  fd_pseudo_cond                          1
% 7.33/1.44  AC symbols                              0
% 7.33/1.44  
% 7.33/1.44  ------ Schedule dynamic 5 is on 
% 7.33/1.44  
% 7.33/1.44  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.33/1.44  
% 7.33/1.44  
% 7.33/1.44  ------ 
% 7.33/1.44  Current options:
% 7.33/1.44  ------ 
% 7.33/1.44  
% 7.33/1.44  ------ Input Options
% 7.33/1.44  
% 7.33/1.44  --out_options                           all
% 7.33/1.44  --tptp_safe_out                         true
% 7.33/1.44  --problem_path                          ""
% 7.33/1.44  --include_path                          ""
% 7.33/1.44  --clausifier                            res/vclausify_rel
% 7.33/1.44  --clausifier_options                    ""
% 7.33/1.44  --stdin                                 false
% 7.33/1.44  --stats_out                             all
% 7.33/1.44  
% 7.33/1.44  ------ General Options
% 7.33/1.44  
% 7.33/1.44  --fof                                   false
% 7.33/1.44  --time_out_real                         305.
% 7.33/1.44  --time_out_virtual                      -1.
% 7.33/1.44  --symbol_type_check                     false
% 7.33/1.44  --clausify_out                          false
% 7.33/1.44  --sig_cnt_out                           false
% 7.33/1.44  --trig_cnt_out                          false
% 7.33/1.44  --trig_cnt_out_tolerance                1.
% 7.33/1.44  --trig_cnt_out_sk_spl                   false
% 7.33/1.44  --abstr_cl_out                          false
% 7.33/1.44  
% 7.33/1.44  ------ Global Options
% 7.33/1.44  
% 7.33/1.44  --schedule                              default
% 7.33/1.44  --add_important_lit                     false
% 7.33/1.44  --prop_solver_per_cl                    1000
% 7.33/1.44  --min_unsat_core                        false
% 7.33/1.44  --soft_assumptions                      false
% 7.33/1.44  --soft_lemma_size                       3
% 7.33/1.44  --prop_impl_unit_size                   0
% 7.33/1.44  --prop_impl_unit                        []
% 7.33/1.44  --share_sel_clauses                     true
% 7.33/1.44  --reset_solvers                         false
% 7.33/1.44  --bc_imp_inh                            [conj_cone]
% 7.33/1.44  --conj_cone_tolerance                   3.
% 7.33/1.44  --extra_neg_conj                        none
% 7.33/1.44  --large_theory_mode                     true
% 7.33/1.44  --prolific_symb_bound                   200
% 7.33/1.44  --lt_threshold                          2000
% 7.33/1.44  --clause_weak_htbl                      true
% 7.33/1.44  --gc_record_bc_elim                     false
% 7.33/1.44  
% 7.33/1.44  ------ Preprocessing Options
% 7.33/1.44  
% 7.33/1.44  --preprocessing_flag                    true
% 7.33/1.44  --time_out_prep_mult                    0.1
% 7.33/1.44  --splitting_mode                        input
% 7.33/1.44  --splitting_grd                         true
% 7.33/1.44  --splitting_cvd                         false
% 7.33/1.44  --splitting_cvd_svl                     false
% 7.33/1.44  --splitting_nvd                         32
% 7.33/1.44  --sub_typing                            true
% 7.33/1.44  --prep_gs_sim                           true
% 7.33/1.44  --prep_unflatten                        true
% 7.33/1.44  --prep_res_sim                          true
% 7.33/1.44  --prep_upred                            true
% 7.33/1.44  --prep_sem_filter                       exhaustive
% 7.33/1.44  --prep_sem_filter_out                   false
% 7.33/1.44  --pred_elim                             true
% 7.33/1.44  --res_sim_input                         true
% 7.33/1.44  --eq_ax_congr_red                       true
% 7.33/1.44  --pure_diseq_elim                       true
% 7.33/1.44  --brand_transform                       false
% 7.33/1.44  --non_eq_to_eq                          false
% 7.33/1.44  --prep_def_merge                        true
% 7.33/1.44  --prep_def_merge_prop_impl              false
% 7.33/1.44  --prep_def_merge_mbd                    true
% 7.33/1.44  --prep_def_merge_tr_red                 false
% 7.33/1.44  --prep_def_merge_tr_cl                  false
% 7.33/1.44  --smt_preprocessing                     true
% 7.33/1.44  --smt_ac_axioms                         fast
% 7.33/1.44  --preprocessed_out                      false
% 7.33/1.44  --preprocessed_stats                    false
% 7.33/1.44  
% 7.33/1.44  ------ Abstraction refinement Options
% 7.33/1.44  
% 7.33/1.44  --abstr_ref                             []
% 7.33/1.44  --abstr_ref_prep                        false
% 7.33/1.44  --abstr_ref_until_sat                   false
% 7.33/1.44  --abstr_ref_sig_restrict                funpre
% 7.33/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.44  --abstr_ref_under                       []
% 7.33/1.44  
% 7.33/1.44  ------ SAT Options
% 7.33/1.44  
% 7.33/1.44  --sat_mode                              false
% 7.33/1.44  --sat_fm_restart_options                ""
% 7.33/1.44  --sat_gr_def                            false
% 7.33/1.44  --sat_epr_types                         true
% 7.33/1.44  --sat_non_cyclic_types                  false
% 7.33/1.44  --sat_finite_models                     false
% 7.33/1.44  --sat_fm_lemmas                         false
% 7.33/1.44  --sat_fm_prep                           false
% 7.33/1.44  --sat_fm_uc_incr                        true
% 7.33/1.44  --sat_out_model                         small
% 7.33/1.44  --sat_out_clauses                       false
% 7.33/1.44  
% 7.33/1.44  ------ QBF Options
% 7.33/1.44  
% 7.33/1.44  --qbf_mode                              false
% 7.33/1.44  --qbf_elim_univ                         false
% 7.33/1.44  --qbf_dom_inst                          none
% 7.33/1.44  --qbf_dom_pre_inst                      false
% 7.33/1.44  --qbf_sk_in                             false
% 7.33/1.44  --qbf_pred_elim                         true
% 7.33/1.44  --qbf_split                             512
% 7.33/1.44  
% 7.33/1.44  ------ BMC1 Options
% 7.33/1.44  
% 7.33/1.44  --bmc1_incremental                      false
% 7.33/1.44  --bmc1_axioms                           reachable_all
% 7.33/1.44  --bmc1_min_bound                        0
% 7.33/1.44  --bmc1_max_bound                        -1
% 7.33/1.44  --bmc1_max_bound_default                -1
% 7.33/1.44  --bmc1_symbol_reachability              true
% 7.33/1.44  --bmc1_property_lemmas                  false
% 7.33/1.44  --bmc1_k_induction                      false
% 7.33/1.44  --bmc1_non_equiv_states                 false
% 7.33/1.44  --bmc1_deadlock                         false
% 7.33/1.44  --bmc1_ucm                              false
% 7.33/1.44  --bmc1_add_unsat_core                   none
% 7.33/1.44  --bmc1_unsat_core_children              false
% 7.33/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.33/1.44  --bmc1_out_stat                         full
% 7.33/1.44  --bmc1_ground_init                      false
% 7.33/1.44  --bmc1_pre_inst_next_state              false
% 7.33/1.44  --bmc1_pre_inst_state                   false
% 7.33/1.44  --bmc1_pre_inst_reach_state             false
% 7.33/1.44  --bmc1_out_unsat_core                   false
% 7.33/1.44  --bmc1_aig_witness_out                  false
% 7.33/1.44  --bmc1_verbose                          false
% 7.33/1.44  --bmc1_dump_clauses_tptp                false
% 7.33/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.33/1.44  --bmc1_dump_file                        -
% 7.33/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.33/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.33/1.44  --bmc1_ucm_extend_mode                  1
% 7.33/1.44  --bmc1_ucm_init_mode                    2
% 7.33/1.44  --bmc1_ucm_cone_mode                    none
% 7.33/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.33/1.44  --bmc1_ucm_relax_model                  4
% 7.33/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.33/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.33/1.44  --bmc1_ucm_layered_model                none
% 7.33/1.44  --bmc1_ucm_max_lemma_size               10
% 7.33/1.44  
% 7.33/1.44  ------ AIG Options
% 7.33/1.44  
% 7.33/1.44  --aig_mode                              false
% 7.33/1.44  
% 7.33/1.44  ------ Instantiation Options
% 7.33/1.44  
% 7.33/1.44  --instantiation_flag                    true
% 7.33/1.44  --inst_sos_flag                         true
% 7.33/1.44  --inst_sos_phase                        true
% 7.33/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.33/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.33/1.44  --inst_lit_sel_side                     none
% 7.33/1.44  --inst_solver_per_active                1400
% 7.33/1.44  --inst_solver_calls_frac                1.
% 7.33/1.44  --inst_passive_queue_type               priority_queues
% 7.33/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.33/1.44  --inst_passive_queues_freq              [25;2]
% 7.33/1.44  --inst_dismatching                      true
% 7.33/1.44  --inst_eager_unprocessed_to_passive     true
% 7.33/1.44  --inst_prop_sim_given                   true
% 7.33/1.44  --inst_prop_sim_new                     false
% 7.33/1.44  --inst_subs_new                         false
% 7.33/1.44  --inst_eq_res_simp                      false
% 7.33/1.44  --inst_subs_given                       false
% 7.33/1.44  --inst_orphan_elimination               true
% 7.33/1.44  --inst_learning_loop_flag               true
% 7.33/1.44  --inst_learning_start                   3000
% 7.33/1.44  --inst_learning_factor                  2
% 7.33/1.44  --inst_start_prop_sim_after_learn       3
% 7.33/1.44  --inst_sel_renew                        solver
% 7.33/1.44  --inst_lit_activity_flag                true
% 7.33/1.44  --inst_restr_to_given                   false
% 7.33/1.44  --inst_activity_threshold               500
% 7.33/1.44  --inst_out_proof                        true
% 7.33/1.44  
% 7.33/1.44  ------ Resolution Options
% 7.33/1.44  
% 7.33/1.44  --resolution_flag                       false
% 7.33/1.44  --res_lit_sel                           adaptive
% 7.33/1.44  --res_lit_sel_side                      none
% 7.33/1.44  --res_ordering                          kbo
% 7.33/1.44  --res_to_prop_solver                    active
% 7.33/1.44  --res_prop_simpl_new                    false
% 7.33/1.44  --res_prop_simpl_given                  true
% 7.33/1.44  --res_passive_queue_type                priority_queues
% 7.33/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.33/1.44  --res_passive_queues_freq               [15;5]
% 7.33/1.44  --res_forward_subs                      full
% 7.33/1.44  --res_backward_subs                     full
% 7.33/1.44  --res_forward_subs_resolution           true
% 7.33/1.44  --res_backward_subs_resolution          true
% 7.33/1.44  --res_orphan_elimination                true
% 7.33/1.44  --res_time_limit                        2.
% 7.33/1.44  --res_out_proof                         true
% 7.33/1.44  
% 7.33/1.44  ------ Superposition Options
% 7.33/1.44  
% 7.33/1.44  --superposition_flag                    true
% 7.33/1.44  --sup_passive_queue_type                priority_queues
% 7.33/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.33/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.33/1.44  --demod_completeness_check              fast
% 7.33/1.44  --demod_use_ground                      true
% 7.33/1.44  --sup_to_prop_solver                    passive
% 7.33/1.44  --sup_prop_simpl_new                    true
% 7.33/1.44  --sup_prop_simpl_given                  true
% 7.33/1.44  --sup_fun_splitting                     true
% 7.33/1.44  --sup_smt_interval                      50000
% 7.33/1.44  
% 7.33/1.44  ------ Superposition Simplification Setup
% 7.33/1.44  
% 7.33/1.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.33/1.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.33/1.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.33/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.33/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.33/1.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.33/1.44  --sup_immed_triv                        [TrivRules]
% 7.33/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.44  --sup_immed_bw_main                     []
% 7.33/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.33/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.33/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.44  --sup_input_bw                          []
% 7.33/1.44  
% 7.33/1.44  ------ Combination Options
% 7.33/1.44  
% 7.33/1.44  --comb_res_mult                         3
% 7.33/1.44  --comb_sup_mult                         2
% 7.33/1.44  --comb_inst_mult                        10
% 7.33/1.44  
% 7.33/1.44  ------ Debug Options
% 7.33/1.44  
% 7.33/1.44  --dbg_backtrace                         false
% 7.33/1.44  --dbg_dump_prop_clauses                 false
% 7.33/1.44  --dbg_dump_prop_clauses_file            -
% 7.33/1.44  --dbg_out_stat                          false
% 7.33/1.44  
% 7.33/1.44  
% 7.33/1.44  
% 7.33/1.44  
% 7.33/1.44  ------ Proving...
% 7.33/1.44  
% 7.33/1.44  
% 7.33/1.44  % SZS status Theorem for theBenchmark.p
% 7.33/1.44  
% 7.33/1.44   Resolution empty clause
% 7.33/1.44  
% 7.33/1.44  % SZS output start CNFRefutation for theBenchmark.p
% 7.33/1.44  
% 7.33/1.44  fof(f16,conjecture,(
% 7.33/1.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f17,negated_conjecture,(
% 7.33/1.44    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.33/1.44    inference(negated_conjecture,[],[f16])).
% 7.33/1.44  
% 7.33/1.44  fof(f37,plain,(
% 7.33/1.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.33/1.44    inference(ennf_transformation,[],[f17])).
% 7.33/1.44  
% 7.33/1.44  fof(f38,plain,(
% 7.33/1.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.33/1.44    inference(flattening,[],[f37])).
% 7.33/1.44  
% 7.33/1.44  fof(f55,plain,(
% 7.33/1.44    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 7.33/1.44    introduced(choice_axiom,[])).
% 7.33/1.44  
% 7.33/1.44  fof(f54,plain,(
% 7.33/1.44    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 7.33/1.44    introduced(choice_axiom,[])).
% 7.33/1.44  
% 7.33/1.44  fof(f53,plain,(
% 7.33/1.44    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 7.33/1.44    introduced(choice_axiom,[])).
% 7.33/1.44  
% 7.33/1.44  fof(f52,plain,(
% 7.33/1.44    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.33/1.44    introduced(choice_axiom,[])).
% 7.33/1.44  
% 7.33/1.44  fof(f51,plain,(
% 7.33/1.44    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 7.33/1.44    introduced(choice_axiom,[])).
% 7.33/1.44  
% 7.33/1.44  fof(f50,plain,(
% 7.33/1.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 7.33/1.44    introduced(choice_axiom,[])).
% 7.33/1.44  
% 7.33/1.44  fof(f56,plain,(
% 7.33/1.44    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.33/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f38,f55,f54,f53,f52,f51,f50])).
% 7.33/1.44  
% 7.33/1.44  fof(f88,plain,(
% 7.33/1.44    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f5,axiom,(
% 7.33/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f21,plain,(
% 7.33/1.44    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.33/1.44    inference(ennf_transformation,[],[f5])).
% 7.33/1.44  
% 7.33/1.44  fof(f65,plain,(
% 7.33/1.44    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.33/1.44    inference(cnf_transformation,[],[f21])).
% 7.33/1.44  
% 7.33/1.44  fof(f6,axiom,(
% 7.33/1.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f66,plain,(
% 7.33/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.33/1.44    inference(cnf_transformation,[],[f6])).
% 7.33/1.44  
% 7.33/1.44  fof(f100,plain,(
% 7.33/1.44    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.33/1.44    inference(definition_unfolding,[],[f65,f66])).
% 7.33/1.44  
% 7.33/1.44  fof(f92,plain,(
% 7.33/1.44    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f13,axiom,(
% 7.33/1.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f31,plain,(
% 7.33/1.44    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.33/1.44    inference(ennf_transformation,[],[f13])).
% 7.33/1.44  
% 7.33/1.44  fof(f32,plain,(
% 7.33/1.44    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.33/1.44    inference(flattening,[],[f31])).
% 7.33/1.44  
% 7.33/1.44  fof(f76,plain,(
% 7.33/1.44    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f32])).
% 7.33/1.44  
% 7.33/1.44  fof(f90,plain,(
% 7.33/1.44    v1_funct_1(sK6)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f95,plain,(
% 7.33/1.44    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f93,plain,(
% 7.33/1.44    v1_funct_1(sK7)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f14,axiom,(
% 7.33/1.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f33,plain,(
% 7.33/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.33/1.44    inference(ennf_transformation,[],[f14])).
% 7.33/1.44  
% 7.33/1.44  fof(f34,plain,(
% 7.33/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.33/1.44    inference(flattening,[],[f33])).
% 7.33/1.44  
% 7.33/1.44  fof(f48,plain,(
% 7.33/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.33/1.44    inference(nnf_transformation,[],[f34])).
% 7.33/1.44  
% 7.33/1.44  fof(f49,plain,(
% 7.33/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.33/1.44    inference(flattening,[],[f48])).
% 7.33/1.44  
% 7.33/1.44  fof(f77,plain,(
% 7.33/1.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f49])).
% 7.33/1.44  
% 7.33/1.44  fof(f105,plain,(
% 7.33/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.44    inference(equality_resolution,[],[f77])).
% 7.33/1.44  
% 7.33/1.44  fof(f15,axiom,(
% 7.33/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f35,plain,(
% 7.33/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.33/1.44    inference(ennf_transformation,[],[f15])).
% 7.33/1.44  
% 7.33/1.44  fof(f36,plain,(
% 7.33/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.33/1.44    inference(flattening,[],[f35])).
% 7.33/1.44  
% 7.33/1.44  fof(f80,plain,(
% 7.33/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f36])).
% 7.33/1.44  
% 7.33/1.44  fof(f81,plain,(
% 7.33/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f36])).
% 7.33/1.44  
% 7.33/1.44  fof(f82,plain,(
% 7.33/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f36])).
% 7.33/1.44  
% 7.33/1.44  fof(f84,plain,(
% 7.33/1.44    ~v1_xboole_0(sK3)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f87,plain,(
% 7.33/1.44    ~v1_xboole_0(sK5)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f94,plain,(
% 7.33/1.44    v1_funct_2(sK7,sK5,sK3)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f85,plain,(
% 7.33/1.44    ~v1_xboole_0(sK4)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f91,plain,(
% 7.33/1.44    v1_funct_2(sK6,sK4,sK3)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f8,axiom,(
% 7.33/1.44    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f23,plain,(
% 7.33/1.44    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.33/1.44    inference(ennf_transformation,[],[f8])).
% 7.33/1.44  
% 7.33/1.44  fof(f24,plain,(
% 7.33/1.44    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.33/1.44    inference(flattening,[],[f23])).
% 7.33/1.44  
% 7.33/1.44  fof(f46,plain,(
% 7.33/1.44    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.33/1.44    inference(nnf_transformation,[],[f24])).
% 7.33/1.44  
% 7.33/1.44  fof(f68,plain,(
% 7.33/1.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f46])).
% 7.33/1.44  
% 7.33/1.44  fof(f89,plain,(
% 7.33/1.44    r1_subset_1(sK4,sK5)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f2,axiom,(
% 7.33/1.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f43,plain,(
% 7.33/1.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.33/1.44    inference(nnf_transformation,[],[f2])).
% 7.33/1.44  
% 7.33/1.44  fof(f59,plain,(
% 7.33/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f43])).
% 7.33/1.44  
% 7.33/1.44  fof(f98,plain,(
% 7.33/1.44    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.33/1.44    inference(definition_unfolding,[],[f59,f66])).
% 7.33/1.44  
% 7.33/1.44  fof(f83,plain,(
% 7.33/1.44    ~v1_xboole_0(sK2)),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f86,plain,(
% 7.33/1.44    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f9,axiom,(
% 7.33/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f25,plain,(
% 7.33/1.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.33/1.44    inference(ennf_transformation,[],[f9])).
% 7.33/1.44  
% 7.33/1.44  fof(f70,plain,(
% 7.33/1.44    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.33/1.44    inference(cnf_transformation,[],[f25])).
% 7.33/1.44  
% 7.33/1.44  fof(f3,axiom,(
% 7.33/1.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f18,plain,(
% 7.33/1.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.33/1.44    inference(rectify,[],[f3])).
% 7.33/1.44  
% 7.33/1.44  fof(f20,plain,(
% 7.33/1.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.33/1.44    inference(ennf_transformation,[],[f18])).
% 7.33/1.44  
% 7.33/1.44  fof(f44,plain,(
% 7.33/1.44    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.33/1.44    introduced(choice_axiom,[])).
% 7.33/1.44  
% 7.33/1.44  fof(f45,plain,(
% 7.33/1.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.33/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f44])).
% 7.33/1.44  
% 7.33/1.44  fof(f61,plain,(
% 7.33/1.44    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f45])).
% 7.33/1.44  
% 7.33/1.44  fof(f4,axiom,(
% 7.33/1.44    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f64,plain,(
% 7.33/1.44    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.33/1.44    inference(cnf_transformation,[],[f4])).
% 7.33/1.44  
% 7.33/1.44  fof(f99,plain,(
% 7.33/1.44    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 7.33/1.44    inference(definition_unfolding,[],[f64,f66])).
% 7.33/1.44  
% 7.33/1.44  fof(f60,plain,(
% 7.33/1.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.33/1.44    inference(cnf_transformation,[],[f43])).
% 7.33/1.44  
% 7.33/1.44  fof(f97,plain,(
% 7.33/1.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.33/1.44    inference(definition_unfolding,[],[f60,f66])).
% 7.33/1.44  
% 7.33/1.44  fof(f63,plain,(
% 7.33/1.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f45])).
% 7.33/1.44  
% 7.33/1.44  fof(f7,axiom,(
% 7.33/1.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.33/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.44  
% 7.33/1.44  fof(f22,plain,(
% 7.33/1.44    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.33/1.44    inference(ennf_transformation,[],[f7])).
% 7.33/1.44  
% 7.33/1.44  fof(f67,plain,(
% 7.33/1.44    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f22])).
% 7.33/1.44  
% 7.33/1.44  fof(f96,plain,(
% 7.33/1.44    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 7.33/1.44    inference(cnf_transformation,[],[f56])).
% 7.33/1.44  
% 7.33/1.44  fof(f78,plain,(
% 7.33/1.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.44    inference(cnf_transformation,[],[f49])).
% 7.33/1.44  
% 7.33/1.44  fof(f104,plain,(
% 7.33/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.44    inference(equality_resolution,[],[f78])).
% 7.33/1.44  
% 7.33/1.44  cnf(c_33,negated_conjecture,
% 7.33/1.44      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.33/1.44      inference(cnf_transformation,[],[f88]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1227,negated_conjecture,
% 7.33/1.44      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_33]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2053,plain,
% 7.33/1.44      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_8,plain,
% 7.33/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.33/1.44      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.33/1.44      inference(cnf_transformation,[],[f100]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1242,plain,
% 7.33/1.44      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.33/1.44      | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_8]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2039,plain,
% 7.33/1.44      ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
% 7.33/1.44      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3184,plain,
% 7.33/1.44      ( k9_subset_1(sK2,X0_57,sK5) = k1_setfam_1(k2_tarski(X0_57,sK5)) ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_2053,c_2039]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_29,negated_conjecture,
% 7.33/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.33/1.44      inference(cnf_transformation,[],[f92]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1230,negated_conjecture,
% 7.33/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_29]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2050,plain,
% 7.33/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_18,plain,
% 7.33/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.33/1.44      inference(cnf_transformation,[],[f76]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1239,plain,
% 7.33/1.44      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.33/1.44      | ~ v1_funct_1(X0_57)
% 7.33/1.44      | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_18]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2042,plain,
% 7.33/1.44      ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
% 7.33/1.44      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.33/1.44      | v1_funct_1(X2_57) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1239]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3981,plain,
% 7.33/1.44      ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57)
% 7.33/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_2050,c_2042]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_31,negated_conjecture,
% 7.33/1.44      ( v1_funct_1(sK6) ),
% 7.33/1.44      inference(cnf_transformation,[],[f90]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_46,plain,
% 7.33/1.44      ( v1_funct_1(sK6) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4103,plain,
% 7.33/1.44      ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
% 7.33/1.44      inference(global_propositional_subsumption,[status(thm)],[c_3981,c_46]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_26,negated_conjecture,
% 7.33/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.33/1.44      inference(cnf_transformation,[],[f95]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1233,negated_conjecture,
% 7.33/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_26]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2047,plain,
% 7.33/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3980,plain,
% 7.33/1.44      ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57)
% 7.33/1.44      | v1_funct_1(sK7) != iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_2047,c_2042]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_28,negated_conjecture,
% 7.33/1.44      ( v1_funct_1(sK7) ),
% 7.33/1.44      inference(cnf_transformation,[],[f93]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_49,plain,
% 7.33/1.44      ( v1_funct_1(sK7) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4098,plain,
% 7.33/1.44      ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
% 7.33/1.44      inference(global_propositional_subsumption,[status(thm)],[c_3980,c_49]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_21,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_1(X3)
% 7.33/1.44      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X1)
% 7.33/1.44      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.33/1.44      inference(cnf_transformation,[],[f105]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_24,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_1(X3)
% 7.33/1.44      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X1) ),
% 7.33/1.44      inference(cnf_transformation,[],[f80]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_23,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_1(X3)
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X1) ),
% 7.33/1.44      inference(cnf_transformation,[],[f81]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_22,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_1(X3)
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X1) ),
% 7.33/1.44      inference(cnf_transformation,[],[f82]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_208,plain,
% 7.33/1.44      ( ~ v1_funct_1(X3)
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X1)
% 7.33/1.44      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.33/1.44      inference(global_propositional_subsumption,
% 7.33/1.44                [status(thm)],
% 7.33/1.44                [c_21,c_24,c_23,c_22]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_209,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_1(X3)
% 7.33/1.44      | v1_xboole_0(X1)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.33/1.44      inference(renaming,[status(thm)],[c_208]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1221,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.33/1.44      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.33/1.44      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.33/1.44      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.33/1.44      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.33/1.44      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.33/1.44      | ~ v1_funct_1(X0_57)
% 7.33/1.44      | ~ v1_funct_1(X3_57)
% 7.33/1.44      | v1_xboole_0(X2_57)
% 7.33/1.44      | v1_xboole_0(X1_57)
% 7.33/1.44      | v1_xboole_0(X4_57)
% 7.33/1.44      | v1_xboole_0(X5_57)
% 7.33/1.44      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_209]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2059,plain,
% 7.33/1.44      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
% 7.33/1.44      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.33/1.44      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.33/1.44      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.33/1.44      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.33/1.44      | v1_funct_1(X2_57) != iProver_top
% 7.33/1.44      | v1_funct_1(X5_57) != iProver_top
% 7.33/1.44      | v1_xboole_0(X3_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X4_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X1_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1221]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4682,plain,
% 7.33/1.44      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.33/1.44      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.33/1.44      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.33/1.44      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.33/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | v1_funct_1(X1_57) != iProver_top
% 7.33/1.44      | v1_funct_1(sK7) != iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X2_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(sK3) = iProver_top
% 7.33/1.44      | v1_xboole_0(sK5) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_4098,c_2059]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_37,negated_conjecture,
% 7.33/1.44      ( ~ v1_xboole_0(sK3) ),
% 7.33/1.44      inference(cnf_transformation,[],[f84]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_40,plain,
% 7.33/1.44      ( v1_xboole_0(sK3) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_34,negated_conjecture,
% 7.33/1.44      ( ~ v1_xboole_0(sK5) ),
% 7.33/1.44      inference(cnf_transformation,[],[f87]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_43,plain,
% 7.33/1.44      ( v1_xboole_0(sK5) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_27,negated_conjecture,
% 7.33/1.44      ( v1_funct_2(sK7,sK5,sK3) ),
% 7.33/1.44      inference(cnf_transformation,[],[f94]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_50,plain,
% 7.33/1.44      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_51,plain,
% 7.33/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4937,plain,
% 7.33/1.44      ( v1_funct_1(X1_57) != iProver_top
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.33/1.44      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.33/1.44      | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.33/1.44      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X2_57) = iProver_top ),
% 7.33/1.44      inference(global_propositional_subsumption,
% 7.33/1.44                [status(thm)],
% 7.33/1.44                [c_4682,c_40,c_43,c_49,c_50,c_51]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4938,plain,
% 7.33/1.44      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.33/1.44      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.33/1.44      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | v1_funct_1(X1_57) != iProver_top
% 7.33/1.44      | v1_xboole_0(X2_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top ),
% 7.33/1.44      inference(renaming,[status(thm)],[c_4937]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4944,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.33/1.44      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.33/1.44      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.33/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | v1_funct_1(sK6) != iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(sK4) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_4103,c_4938]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_36,negated_conjecture,
% 7.33/1.44      ( ~ v1_xboole_0(sK4) ),
% 7.33/1.44      inference(cnf_transformation,[],[f85]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_41,plain,
% 7.33/1.44      ( v1_xboole_0(sK4) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_30,negated_conjecture,
% 7.33/1.44      ( v1_funct_2(sK6,sK4,sK3) ),
% 7.33/1.44      inference(cnf_transformation,[],[f91]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_47,plain,
% 7.33/1.44      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_48,plain,
% 7.33/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5045,plain,
% 7.33/1.44      ( v1_xboole_0(X0_57) = iProver_top
% 7.33/1.44      | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.33/1.44      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.33/1.44      inference(global_propositional_subsumption,
% 7.33/1.44                [status(thm)],
% 7.33/1.44                [c_4944,c_41,c_46,c_47,c_48]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5046,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.33/1.44      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top ),
% 7.33/1.44      inference(renaming,[status(thm)],[c_5045]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5051,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.33/1.44      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_3184,c_5046]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_11,plain,
% 7.33/1.44      ( ~ r1_subset_1(X0,X1)
% 7.33/1.44      | r1_xboole_0(X0,X1)
% 7.33/1.44      | v1_xboole_0(X0)
% 7.33/1.44      | v1_xboole_0(X1) ),
% 7.33/1.44      inference(cnf_transformation,[],[f68]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_32,negated_conjecture,
% 7.33/1.44      ( r1_subset_1(sK4,sK5) ),
% 7.33/1.44      inference(cnf_transformation,[],[f89]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_556,plain,
% 7.33/1.44      ( r1_xboole_0(X0,X1)
% 7.33/1.44      | v1_xboole_0(X0)
% 7.33/1.44      | v1_xboole_0(X1)
% 7.33/1.44      | sK5 != X1
% 7.33/1.44      | sK4 != X0 ),
% 7.33/1.44      inference(resolution_lifted,[status(thm)],[c_11,c_32]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_557,plain,
% 7.33/1.44      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 7.33/1.44      inference(unflattening,[status(thm)],[c_556]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_559,plain,
% 7.33/1.44      ( r1_xboole_0(sK4,sK5) ),
% 7.33/1.44      inference(global_propositional_subsumption,
% 7.33/1.44                [status(thm)],
% 7.33/1.44                [c_557,c_36,c_34]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1219,plain,
% 7.33/1.44      ( r1_xboole_0(sK4,sK5) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_559]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2061,plain,
% 7.33/1.44      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1219]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3,plain,
% 7.33/1.44      ( ~ r1_xboole_0(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.33/1.44      inference(cnf_transformation,[],[f98]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1247,plain,
% 7.33/1.44      ( ~ r1_xboole_0(X0_57,X1_57)
% 7.33/1.44      | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_3]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2035,plain,
% 7.33/1.44      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
% 7.33/1.44      | r1_xboole_0(X0_57,X1_57) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3092,plain,
% 7.33/1.44      ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_2061,c_2035]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5052,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.33/1.44      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(light_normalisation,[status(thm)],[c_5051,c_3092]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5053,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.33/1.44      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0)
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(demodulation,[status(thm)],[c_5052,c_3184]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5054,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.33/1.44      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(light_normalisation,[status(thm)],[c_5053,c_3092]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_38,negated_conjecture,
% 7.33/1.44      ( ~ v1_xboole_0(sK2) ),
% 7.33/1.44      inference(cnf_transformation,[],[f83]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_39,plain,
% 7.33/1.44      ( v1_xboole_0(sK2) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_35,negated_conjecture,
% 7.33/1.44      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 7.33/1.44      inference(cnf_transformation,[],[f86]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_42,plain,
% 7.33/1.44      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_44,plain,
% 7.33/1.44      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5055,plain,
% 7.33/1.44      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 7.33/1.44      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 7.33/1.44      | v1_xboole_0(sK2)
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.33/1.44      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.33/1.44      inference(predicate_to_equality_rev,[status(thm)],[c_5054]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_12,plain,
% 7.33/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.33/1.44      inference(cnf_transformation,[],[f70]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1240,plain,
% 7.33/1.44      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.33/1.44      | v1_relat_1(X0_57) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_12]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2041,plain,
% 7.33/1.44      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.33/1.44      | v1_relat_1(X0_57) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3259,plain,
% 7.33/1.44      ( v1_relat_1(sK7) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_2047,c_2041]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_6,plain,
% 7.33/1.44      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.33/1.44      inference(cnf_transformation,[],[f61]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1244,plain,
% 7.33/1.44      ( r1_xboole_0(X0_57,X1_57) | r2_hidden(sK1(X0_57,X1_57),X0_57) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_6]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2038,plain,
% 7.33/1.44      ( r1_xboole_0(X0_57,X1_57) = iProver_top
% 7.33/1.44      | r2_hidden(sK1(X0_57,X1_57),X0_57) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7,plain,
% 7.33/1.44      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.33/1.44      inference(cnf_transformation,[],[f99]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1243,plain,
% 7.33/1.44      ( k1_setfam_1(k2_tarski(X0_57,k1_xboole_0)) = k1_xboole_0 ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_7]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2,plain,
% 7.33/1.44      ( r1_xboole_0(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 7.33/1.44      inference(cnf_transformation,[],[f97]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1248,plain,
% 7.33/1.44      ( r1_xboole_0(X0_57,X1_57)
% 7.33/1.44      | k1_setfam_1(k2_tarski(X0_57,X1_57)) != k1_xboole_0 ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_2]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2034,plain,
% 7.33/1.44      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) != k1_xboole_0
% 7.33/1.44      | r1_xboole_0(X0_57,X1_57) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1248]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3002,plain,
% 7.33/1.44      ( r1_xboole_0(X0_57,k1_xboole_0) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_1243,c_2034]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4,plain,
% 7.33/1.44      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 7.33/1.44      inference(cnf_transformation,[],[f63]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1246,plain,
% 7.33/1.44      ( ~ r1_xboole_0(X0_57,X1_57)
% 7.33/1.44      | ~ r2_hidden(X0_60,X0_57)
% 7.33/1.44      | ~ r2_hidden(X0_60,X1_57) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_4]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2036,plain,
% 7.33/1.44      ( r1_xboole_0(X0_57,X1_57) != iProver_top
% 7.33/1.44      | r2_hidden(X0_60,X1_57) != iProver_top
% 7.33/1.44      | r2_hidden(X0_60,X0_57) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1246]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4000,plain,
% 7.33/1.44      ( r2_hidden(X0_60,X0_57) != iProver_top
% 7.33/1.44      | r2_hidden(X0_60,k1_xboole_0) != iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_3002,c_2036]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4818,plain,
% 7.33/1.44      ( r1_xboole_0(X0_57,X1_57) = iProver_top
% 7.33/1.44      | r2_hidden(sK1(X0_57,X1_57),k1_xboole_0) != iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_2038,c_4000]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5818,plain,
% 7.33/1.44      ( r1_xboole_0(k1_xboole_0,X0_57) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_2038,c_4818]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_9,plain,
% 7.33/1.44      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.33/1.44      | ~ v1_relat_1(X1)
% 7.33/1.44      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.33/1.44      inference(cnf_transformation,[],[f67]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1241,plain,
% 7.33/1.44      ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
% 7.33/1.44      | ~ v1_relat_1(X1_57)
% 7.33/1.44      | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_9]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2040,plain,
% 7.33/1.44      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.33/1.44      | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
% 7.33/1.44      | v1_relat_1(X0_57) != iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5855,plain,
% 7.33/1.44      ( k7_relat_1(X0_57,k1_xboole_0) = k1_xboole_0
% 7.33/1.44      | v1_relat_1(X0_57) != iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_5818,c_2040]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5860,plain,
% 7.33/1.44      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_3259,c_5855]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_25,negated_conjecture,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.33/1.44      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.33/1.44      inference(cnf_transformation,[],[f96]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1234,negated_conjecture,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.33/1.44      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_25]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3866,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.33/1.44      | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 7.33/1.44      inference(demodulation,[status(thm)],[c_3184,c_1234]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3867,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.33/1.44      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
% 7.33/1.44      inference(light_normalisation,[status(thm)],[c_3866,c_3092]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4101,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.33/1.44      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.33/1.44      inference(demodulation,[status(thm)],[c_4098,c_3867]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_4125,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.33/1.44      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.33/1.44      inference(demodulation,[status(thm)],[c_4101,c_4103]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5910,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.33/1.44      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 7.33/1.44      inference(demodulation,[status(thm)],[c_5860,c_4125]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_3260,plain,
% 7.33/1.44      ( v1_relat_1(sK6) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_2050,c_2041]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5861,plain,
% 7.33/1.44      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_3260,c_5855]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5911,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.33/1.44      | k1_xboole_0 != k1_xboole_0 ),
% 7.33/1.44      inference(light_normalisation,[status(thm)],[c_5910,c_5861]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5912,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.33/1.44      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 ),
% 7.33/1.44      inference(equality_resolution_simp,[status(thm)],[c_5911]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_20,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_1(X3)
% 7.33/1.44      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X1)
% 7.33/1.44      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.33/1.44      inference(cnf_transformation,[],[f104]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_215,plain,
% 7.33/1.44      ( ~ v1_funct_1(X3)
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X1)
% 7.33/1.44      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.33/1.44      inference(global_propositional_subsumption,
% 7.33/1.44                [status(thm)],
% 7.33/1.44                [c_20,c_24,c_23,c_22]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_216,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.44      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.44      | ~ v1_funct_1(X0)
% 7.33/1.44      | ~ v1_funct_1(X3)
% 7.33/1.44      | v1_xboole_0(X1)
% 7.33/1.44      | v1_xboole_0(X2)
% 7.33/1.44      | v1_xboole_0(X4)
% 7.33/1.44      | v1_xboole_0(X5)
% 7.33/1.44      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.33/1.44      inference(renaming,[status(thm)],[c_215]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_1220,plain,
% 7.33/1.44      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.33/1.44      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.33/1.44      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.33/1.44      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.33/1.44      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.33/1.44      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.33/1.44      | ~ v1_funct_1(X0_57)
% 7.33/1.44      | ~ v1_funct_1(X3_57)
% 7.33/1.44      | v1_xboole_0(X2_57)
% 7.33/1.44      | v1_xboole_0(X1_57)
% 7.33/1.44      | v1_xboole_0(X4_57)
% 7.33/1.44      | v1_xboole_0(X5_57)
% 7.33/1.44      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
% 7.33/1.44      inference(subtyping,[status(esa)],[c_216]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_2060,plain,
% 7.33/1.44      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
% 7.33/1.44      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.33/1.44      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.33/1.44      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.33/1.44      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.33/1.44      | v1_funct_1(X2_57) != iProver_top
% 7.33/1.44      | v1_funct_1(X5_57) != iProver_top
% 7.33/1.44      | v1_xboole_0(X3_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X4_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X1_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top ),
% 7.33/1.44      inference(predicate_to_equality,[status(thm)],[c_1220]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_5774,plain,
% 7.33/1.44      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.33/1.44      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.33/1.44      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.33/1.44      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.33/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | v1_funct_1(X1_57) != iProver_top
% 7.33/1.44      | v1_funct_1(sK7) != iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X2_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(sK3) = iProver_top
% 7.33/1.44      | v1_xboole_0(sK5) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_4098,c_2060]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7279,plain,
% 7.33/1.44      ( v1_funct_1(X1_57) != iProver_top
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.33/1.44      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.33/1.44      | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.33/1.44      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X2_57) = iProver_top ),
% 7.33/1.44      inference(global_propositional_subsumption,
% 7.33/1.44                [status(thm)],
% 7.33/1.44                [c_5774,c_40,c_43,c_49,c_50,c_51]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7280,plain,
% 7.33/1.44      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.33/1.44      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.33/1.44      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.33/1.44      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.33/1.44      | v1_funct_1(X1_57) != iProver_top
% 7.33/1.44      | v1_xboole_0(X2_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top ),
% 7.33/1.44      inference(renaming,[status(thm)],[c_7279]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7286,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.33/1.44      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.33/1.44      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.33/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | v1_funct_1(sK6) != iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top
% 7.33/1.44      | v1_xboole_0(sK4) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_4103,c_7280]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7296,plain,
% 7.33/1.44      ( v1_xboole_0(X0_57) = iProver_top
% 7.33/1.44      | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.33/1.44      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.33/1.44      inference(global_propositional_subsumption,
% 7.33/1.44                [status(thm)],
% 7.33/1.44                [c_7286,c_41,c_46,c_47,c_48]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7297,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.33/1.44      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.33/1.44      | v1_xboole_0(X0_57) = iProver_top ),
% 7.33/1.44      inference(renaming,[status(thm)],[c_7296]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7302,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.33/1.44      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(superposition,[status(thm)],[c_3184,c_7297]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7303,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.33/1.44      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(light_normalisation,[status(thm)],[c_7302,c_3092,c_5860]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7304,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.33/1.44      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k1_xboole_0
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(demodulation,[status(thm)],[c_7303,c_3184]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7305,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.33/1.44      | k1_xboole_0 != k1_xboole_0
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(light_normalisation,[status(thm)],[c_7304,c_3092,c_5861]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_7306,plain,
% 7.33/1.44      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.33/1.44      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.33/1.44      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.44      inference(equality_resolution_simp,[status(thm)],[c_7305]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_13786,plain,
% 7.33/1.44      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.33/1.44      inference(global_propositional_subsumption,
% 7.33/1.44                [status(thm)],
% 7.33/1.44                [c_5054,c_38,c_39,c_35,c_42,c_33,c_44,c_5055,c_5912,c_7306]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_13788,plain,
% 7.33/1.44      ( k1_xboole_0 != k1_xboole_0 ),
% 7.33/1.44      inference(light_normalisation,[status(thm)],[c_13786,c_5860,c_5861]) ).
% 7.33/1.44  
% 7.33/1.44  cnf(c_13789,plain,
% 7.33/1.44      ( $false ),
% 7.33/1.44      inference(equality_resolution_simp,[status(thm)],[c_13788]) ).
% 7.33/1.44  
% 7.33/1.44  
% 7.33/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 7.33/1.44  
% 7.33/1.44  ------                               Statistics
% 7.33/1.44  
% 7.33/1.44  ------ General
% 7.33/1.44  
% 7.33/1.44  abstr_ref_over_cycles:                  0
% 7.33/1.44  abstr_ref_under_cycles:                 0
% 7.33/1.44  gc_basic_clause_elim:                   0
% 7.33/1.44  forced_gc_time:                         0
% 7.33/1.44  parsing_time:                           0.011
% 7.33/1.44  unif_index_cands_time:                  0.
% 7.33/1.44  unif_index_add_time:                    0.
% 7.33/1.44  orderings_time:                         0.
% 7.33/1.44  out_proof_time:                         0.015
% 7.33/1.44  total_time:                             0.891
% 7.33/1.44  num_of_symbols:                         64
% 7.33/1.44  num_of_terms:                           38554
% 7.33/1.44  
% 7.33/1.44  ------ Preprocessing
% 7.33/1.44  
% 7.33/1.44  num_of_splits:                          0
% 7.33/1.44  num_of_split_atoms:                     0
% 7.33/1.44  num_of_reused_defs:                     0
% 7.33/1.44  num_eq_ax_congr_red:                    30
% 7.33/1.44  num_of_sem_filtered_clauses:            1
% 7.33/1.44  num_of_subtypes:                        4
% 7.33/1.44  monotx_restored_types:                  0
% 7.33/1.44  sat_num_of_epr_types:                   0
% 7.33/1.44  sat_num_of_non_cyclic_types:            0
% 7.33/1.44  sat_guarded_non_collapsed_types:        1
% 7.33/1.44  num_pure_diseq_elim:                    0
% 7.33/1.44  simp_replaced_by:                       0
% 7.33/1.44  res_preprocessed:                       176
% 7.33/1.44  prep_upred:                             0
% 7.33/1.44  prep_unflattend:                        30
% 7.33/1.44  smt_new_axioms:                         0
% 7.33/1.44  pred_elim_cands:                        7
% 7.33/1.44  pred_elim:                              3
% 7.33/1.44  pred_elim_cl:                           5
% 7.33/1.44  pred_elim_cycles:                       7
% 7.33/1.44  merged_defs:                            8
% 7.33/1.44  merged_defs_ncl:                        0
% 7.33/1.44  bin_hyper_res:                          8
% 7.33/1.44  prep_cycles:                            4
% 7.33/1.44  pred_elim_time:                         0.008
% 7.33/1.44  splitting_time:                         0.
% 7.33/1.44  sem_filter_time:                        0.
% 7.33/1.44  monotx_time:                            0.
% 7.33/1.44  subtype_inf_time:                       0.001
% 7.33/1.44  
% 7.33/1.44  ------ Problem properties
% 7.33/1.44  
% 7.33/1.44  clauses:                                33
% 7.33/1.44  conjectures:                            13
% 7.33/1.44  epr:                                    11
% 7.33/1.44  horn:                                   23
% 7.33/1.44  ground:                                 14
% 7.33/1.44  unary:                                  14
% 7.33/1.44  binary:                                 8
% 7.33/1.44  lits:                                   131
% 7.33/1.44  lits_eq:                                16
% 7.33/1.44  fd_pure:                                0
% 7.33/1.44  fd_pseudo:                              0
% 7.33/1.44  fd_cond:                                0
% 7.33/1.44  fd_pseudo_cond:                         1
% 7.33/1.44  ac_symbols:                             0
% 7.33/1.44  
% 7.33/1.44  ------ Propositional Solver
% 7.33/1.44  
% 7.33/1.44  prop_solver_calls:                      31
% 7.33/1.44  prop_fast_solver_calls:                 3495
% 7.33/1.44  smt_solver_calls:                       0
% 7.33/1.44  smt_fast_solver_calls:                  0
% 7.33/1.44  prop_num_of_clauses:                    7539
% 7.33/1.44  prop_preprocess_simplified:             16058
% 7.33/1.44  prop_fo_subsumed:                       268
% 7.33/1.44  prop_solver_time:                       0.
% 7.33/1.44  smt_solver_time:                        0.
% 7.33/1.44  smt_fast_solver_time:                   0.
% 7.33/1.44  prop_fast_solver_time:                  0.
% 7.33/1.44  prop_unsat_core_time:                   0.
% 7.33/1.44  
% 7.33/1.44  ------ QBF
% 7.33/1.44  
% 7.33/1.44  qbf_q_res:                              0
% 7.33/1.44  qbf_num_tautologies:                    0
% 7.33/1.44  qbf_prep_cycles:                        0
% 7.33/1.44  
% 7.33/1.44  ------ BMC1
% 7.33/1.44  
% 7.33/1.44  bmc1_current_bound:                     -1
% 7.33/1.44  bmc1_last_solved_bound:                 -1
% 7.33/1.44  bmc1_unsat_core_size:                   -1
% 7.33/1.44  bmc1_unsat_core_parents_size:           -1
% 7.33/1.44  bmc1_merge_next_fun:                    0
% 7.33/1.44  bmc1_unsat_core_clauses_time:           0.
% 7.33/1.44  
% 7.33/1.44  ------ Instantiation
% 7.33/1.44  
% 7.33/1.44  inst_num_of_clauses:                    1663
% 7.33/1.44  inst_num_in_passive:                    621
% 7.33/1.44  inst_num_in_active:                     749
% 7.33/1.44  inst_num_in_unprocessed:                293
% 7.33/1.44  inst_num_of_loops:                      950
% 7.33/1.44  inst_num_of_learning_restarts:          0
% 7.33/1.44  inst_num_moves_active_passive:          199
% 7.33/1.44  inst_lit_activity:                      0
% 7.33/1.44  inst_lit_activity_moves:                2
% 7.33/1.44  inst_num_tautologies:                   0
% 7.33/1.44  inst_num_prop_implied:                  0
% 7.33/1.44  inst_num_existing_simplified:           0
% 7.33/1.44  inst_num_eq_res_simplified:             0
% 7.33/1.44  inst_num_child_elim:                    0
% 7.33/1.44  inst_num_of_dismatching_blockings:      234
% 7.33/1.44  inst_num_of_non_proper_insts:           1710
% 7.33/1.44  inst_num_of_duplicates:                 0
% 7.33/1.44  inst_inst_num_from_inst_to_res:         0
% 7.33/1.44  inst_dismatching_checking_time:         0.
% 7.33/1.44  
% 7.33/1.44  ------ Resolution
% 7.33/1.44  
% 7.33/1.44  res_num_of_clauses:                     0
% 7.33/1.44  res_num_in_passive:                     0
% 7.33/1.44  res_num_in_active:                      0
% 7.33/1.44  res_num_of_loops:                       180
% 7.33/1.44  res_forward_subset_subsumed:            29
% 7.33/1.44  res_backward_subset_subsumed:           0
% 7.33/1.44  res_forward_subsumed:                   0
% 7.33/1.44  res_backward_subsumed:                  0
% 7.33/1.44  res_forward_subsumption_resolution:     1
% 7.33/1.44  res_backward_subsumption_resolution:    0
% 7.33/1.44  res_clause_to_clause_subsumption:       870
% 7.33/1.44  res_orphan_elimination:                 0
% 7.33/1.44  res_tautology_del:                      35
% 7.33/1.44  res_num_eq_res_simplified:              0
% 7.33/1.44  res_num_sel_changes:                    0
% 7.33/1.44  res_moves_from_active_to_pass:          0
% 7.33/1.44  
% 7.33/1.44  ------ Superposition
% 7.33/1.44  
% 7.33/1.44  sup_time_total:                         0.
% 7.33/1.44  sup_time_generating:                    0.
% 7.33/1.44  sup_time_sim_full:                      0.
% 7.33/1.44  sup_time_sim_immed:                     0.
% 7.33/1.44  
% 7.33/1.44  sup_num_of_clauses:                     336
% 7.33/1.44  sup_num_in_active:                      175
% 7.33/1.44  sup_num_in_passive:                     161
% 7.33/1.44  sup_num_of_loops:                       189
% 7.33/1.44  sup_fw_superposition:                   270
% 7.33/1.44  sup_bw_superposition:                   123
% 7.33/1.44  sup_immediate_simplified:               150
% 7.33/1.44  sup_given_eliminated:                   0
% 7.33/1.44  comparisons_done:                       0
% 7.33/1.44  comparisons_avoided:                    0
% 7.33/1.44  
% 7.33/1.44  ------ Simplifications
% 7.33/1.44  
% 7.33/1.44  
% 7.33/1.44  sim_fw_subset_subsumed:                 8
% 7.33/1.44  sim_bw_subset_subsumed:                 1
% 7.33/1.44  sim_fw_subsumed:                        17
% 7.33/1.44  sim_bw_subsumed:                        11
% 7.33/1.44  sim_fw_subsumption_res:                 0
% 7.33/1.44  sim_bw_subsumption_res:                 0
% 7.33/1.44  sim_tautology_del:                      1
% 7.33/1.44  sim_eq_tautology_del:                   8
% 7.33/1.44  sim_eq_res_simp:                        7
% 7.33/1.44  sim_fw_demodulated:                     79
% 7.33/1.44  sim_bw_demodulated:                     4
% 7.33/1.44  sim_light_normalised:                   69
% 7.33/1.44  sim_joinable_taut:                      0
% 7.33/1.44  sim_joinable_simp:                      0
% 7.33/1.44  sim_ac_normalised:                      0
% 7.33/1.44  sim_smt_subsumption:                    0
% 7.33/1.44  
%------------------------------------------------------------------------------
