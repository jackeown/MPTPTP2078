%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:26 EST 2020

% Result     : Theorem 15.04s
% Output     : CNFRefutation 15.04s
% Verified   : 
% Statistics : Number of formulae       :  328 (8322 expanded)
%              Number of clauses        :  230 (1920 expanded)
%              Number of leaves         :   25 (3350 expanded)
%              Depth                    :   28
%              Number of atoms          : 1824 (111774 expanded)
%              Number of equality atoms :  931 (27205 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f55,plain,(
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f55,f54,f53,f52,f51,f50])).

fof(f94,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

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
    inference(equality_resolution,[],[f76])).

fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(cnf_transformation,[],[f40])).

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
    inference(cnf_transformation,[],[f40])).

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
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r1_xboole_0(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
     => r1_xboole_0(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f45])).

fof(f70,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(equality_resolution,[],[f77])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f95,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1486,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1491,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4781,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_1491])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2038,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2322,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_2038])).

cnf(c_5057,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4781,c_27,c_25,c_2322])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1479,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1503,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2987,plain,
    ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_1479,c_1503])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1483,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4782,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1491])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2043,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2327,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2043])).

cnf(c_5063,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4782,c_30,c_28,c_2327])).

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
    inference(cnf_transformation,[],[f105])).

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
    inference(cnf_transformation,[],[f79])).

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
    inference(cnf_transformation,[],[f80])).

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
    inference(cnf_transformation,[],[f81])).

cnf(c_371,plain,
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

cnf(c_372,plain,
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
    inference(renaming,[status(thm)],[c_371])).

cnf(c_1473,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1748,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1473,c_1502])).

cnf(c_9374,plain,
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
    inference(superposition,[status(thm)],[c_5063,c_1748])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_32387,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9374,c_39,c_40,c_45,c_46,c_47])).

cnf(c_32388,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_32387])).

cnf(c_32409,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5
    | k2_partfun1(sK4,sK2,X0,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | v1_funct_2(X0,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_32388])).

cnf(c_31,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1480,plain,
    ( r1_subset_1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1498,plain,
    ( r1_subset_1(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3515,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1498])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_42,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_44,plain,
    ( r1_subset_1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1944,plain,
    ( ~ r1_subset_1(sK3,sK4)
    | r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1945,plain,
    ( r1_subset_1(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_3998,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3515,c_40,c_42,c_44,c_1945])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1504,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4004,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3998,c_1504])).

cnf(c_32506,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,X0,k1_xboole_0)
    | v1_funct_2(X0,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_32409,c_4004])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1497,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2680,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1497])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1501,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3075,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK5,X0),X1) ),
    inference(superposition,[status(thm)],[c_2680,c_1501])).

cnf(c_32507,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5
    | k2_partfun1(sK4,sK2,X0,k1_xboole_0) != k7_relat_1(k7_relat_1(sK5,sK3),sK4)
    | v1_funct_2(X0,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32506,c_2987,c_3075])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_43251,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_2(X0,sK4,sK2) != iProver_top
    | k2_partfun1(sK4,sK2,X0,k1_xboole_0) != k7_relat_1(k7_relat_1(sK5,sK3),sK4)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32507,c_41,c_42,c_43])).

cnf(c_43252,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5
    | k2_partfun1(sK4,sK2,X0,k1_xboole_0) != k7_relat_1(k7_relat_1(sK5,sK3),sK4)
    | v1_funct_2(X0,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_43251])).

cnf(c_43262,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k7_relat_1(sK6,k1_xboole_0)
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5057,c_43252])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1494,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2799,plain,
    ( v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_partfun1(sK6,sK4) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_1494])).

cnf(c_48,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_49,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_50,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2028,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2316,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | v1_partfun1(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2028])).

cnf(c_2317,plain,
    ( v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_partfun1(sK6,sK4) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2316])).

cnf(c_4087,plain,
    ( v1_partfun1(sK6,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2799,c_39,c_48,c_49,c_50,c_2317])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1492,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4549,plain,
    ( k1_relat_1(sK6) = sK4
    | v4_relat_1(sK6,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4087,c_1492])).

cnf(c_1922,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1928,plain,
    ( v4_relat_1(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2121,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ v4_relat_1(sK6,X0)
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2872,plain,
    ( ~ v1_partfun1(sK6,sK4)
    | ~ v4_relat_1(sK6,sK4)
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_2121])).

cnf(c_5220,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4549,c_36,c_27,c_26,c_25,c_1922,c_1928,c_2316,c_2872])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1500,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5224,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5220,c_1500])).

cnf(c_1923,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1922])).

cnf(c_7077,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5224,c_50,c_1923])).

cnf(c_7078,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7077])).

cnf(c_7086,plain,
    ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3998,c_7078])).

cnf(c_2679,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_1497])).

cnf(c_3004,plain,
    ( k7_relat_1(sK6,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK6,X0),X1) ),
    inference(superposition,[status(thm)],[c_2679,c_1501])).

cnf(c_4283,plain,
    ( k7_relat_1(k7_relat_1(sK6,sK3),sK4) = k7_relat_1(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4004,c_3004])).

cnf(c_7343,plain,
    ( k7_relat_1(k1_xboole_0,sK4) = k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7086,c_4283])).

cnf(c_6,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7344,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7343,c_6])).

cnf(c_43263,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k1_xboole_0
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_43262,c_7344])).

cnf(c_1489,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1693,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1489,c_1502])).

cnf(c_6794,plain,
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
    inference(superposition,[status(thm)],[c_1693,c_1491])).

cnf(c_1487,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1641,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1487,c_1502])).

cnf(c_17188,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_6794,c_1641])).

cnf(c_17193,plain,
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
    inference(superposition,[status(thm)],[c_1486,c_17188])).

cnf(c_17576,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17193,c_39,c_42,c_48,c_49])).

cnf(c_17577,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_17576])).

cnf(c_17591,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_17577])).

cnf(c_18331,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17591,c_40,c_45,c_46])).

cnf(c_18340,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_18331])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2063,plain,
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
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2404,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK5,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | v1_funct_1(k1_tmap_1(X3,X1,X2,X0,sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3) ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_2947,plain,
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
    inference(instantiation,[status(thm)],[c_2404])).

cnf(c_3237,plain,
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
    inference(instantiation,[status(thm)],[c_2947])).

cnf(c_4532,plain,
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
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_2086,plain,
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
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2424,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK5,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | m1_subset_1(k1_tmap_1(X3,X1,X2,X0,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X0),X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3) ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_2967,plain,
    ( ~ v1_funct_2(sK6,X0,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k1_tmap_1(X1,sK2,sK3,X0,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,sK3,X0),sK2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_3258,plain,
    ( ~ v1_funct_2(sK6,sK4,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | m1_subset_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK3,sK4),sK2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2967])).

cnf(c_4725,plain,
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
    inference(instantiation,[status(thm)],[c_3258])).

cnf(c_6077,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
    | k2_partfun1(X0,X1,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X2) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_13191,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
    | ~ v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_6077])).

cnf(c_18421,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18340,c_37,c_36,c_35,c_34,c_33,c_32,c_30,c_29,c_28,c_27,c_26,c_25,c_4532,c_4725,c_13191])).

cnf(c_43264,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k1_xboole_0
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43263,c_18421])).

cnf(c_1477,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6797,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_1497])).

cnf(c_12,plain,
    ( r1_xboole_0(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1495,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3720,plain,
    ( k7_relat_1(X0,sK0(k1_relat_1(X0))) = k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1500])).

cnf(c_7218,plain,
    ( k7_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),sK0(k1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)))) = k1_xboole_0
    | k1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) = k1_xboole_0
    | v1_funct_2(X5,X3,X1) != iProver_top
    | v1_funct_2(X4,X2,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6797,c_3720])).

cnf(c_21388,plain,
    ( k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)))) = k1_xboole_0
    | k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k1_xboole_0
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_7218])).

cnf(c_22268,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)))) = k1_xboole_0
    | k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k1_xboole_0
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21388,c_39,c_40,c_45,c_46])).

cnf(c_22269,plain,
    ( k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)))) = k1_xboole_0
    | k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k1_xboole_0
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_22268])).

cnf(c_22284,plain,
    ( k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)))) = k1_xboole_0
    | k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_22269])).

cnf(c_22357,plain,
    ( k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0
    | k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)))) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22284,c_40,c_45,c_46])).

cnf(c_22358,plain,
    ( k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)))) = k1_xboole_0
    | k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22357])).

cnf(c_22366,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK0(k1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)))) = k1_xboole_0
    | k1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1477,c_22358])).

cnf(c_6796,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2) != iProver_top
    | v1_partfun1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1)) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_1494])).

cnf(c_1488,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X5) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1667,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1488,c_1502])).

cnf(c_19762,plain,
    ( v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | v1_partfun1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1)) = iProver_top
    | v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6796,c_1667,c_1641])).

cnf(c_19763,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | v1_partfun1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1)) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_19762])).

cnf(c_19780,plain,
    ( k1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) = k4_subset_1(X0,X2,X3)
    | v1_funct_2(X5,X3,X1) != iProver_top
    | v1_funct_2(X4,X2,X1) != iProver_top
    | v4_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19763,c_1492])).

cnf(c_1496,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6795,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | v4_relat_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1)) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_1496])).

cnf(c_20228,plain,
    ( k1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) = k4_subset_1(X0,X2,X3)
    | v1_funct_2(X5,X3,X1) != iProver_top
    | v1_funct_2(X4,X2,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19780,c_6797,c_6795])).

cnf(c_20234,plain,
    ( k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k4_subset_1(X0,X1,sK3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_20228])).

cnf(c_20947,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k4_subset_1(X0,X1,sK3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20234,c_39,c_40,c_45,c_46])).

cnf(c_20948,plain,
    ( k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k4_subset_1(X0,X1,sK3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_20947])).

cnf(c_20962,plain,
    ( k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k4_subset_1(X0,sK3,sK3)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_20948])).

cnf(c_21029,plain,
    ( k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k4_subset_1(X0,sK3,sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20962,c_40,c_45,c_46])).

cnf(c_21037,plain,
    ( k1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) = k4_subset_1(sK1,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1477,c_21029])).

cnf(c_22367,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK0(k4_subset_1(sK1,sK3,sK3))) = k1_xboole_0
    | k1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_22366,c_21037])).

cnf(c_22368,plain,
    ( k4_subset_1(sK1,sK3,sK3) = k1_xboole_0
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK0(k4_subset_1(sK1,sK3,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22367,c_21037])).

cnf(c_17194,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK2,k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_17188])).

cnf(c_18683,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | k2_partfun1(k4_subset_1(X0,X1,sK3),sK2,k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17194,c_39,c_40,c_45,c_46])).

cnf(c_18684,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK2,k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_18683])).

cnf(c_18698,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK3),sK2,k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_18684])).

cnf(c_18985,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK3),sK2,k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1)
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18698,c_40,c_45,c_46])).

cnf(c_18993,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK3),sK2,k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) ),
    inference(superposition,[status(thm)],[c_1477,c_18985])).

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
    inference(cnf_transformation,[],[f104])).

cnf(c_380,plain,
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

cnf(c_381,plain,
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
    inference(renaming,[status(thm)],[c_380])).

cnf(c_1472,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_1720,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1472,c_1502])).

cnf(c_7786,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
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
    inference(superposition,[status(thm)],[c_5063,c_1720])).

cnf(c_10367,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7786,c_39,c_40,c_45,c_46,c_47])).

cnf(c_10368,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10367])).

cnf(c_10382,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK3),sK2,k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5063,c_10368])).

cnf(c_10693,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK3),sK2,k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10382,c_40,c_45,c_46,c_47])).

cnf(c_10701,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK3),sK2,k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_1477,c_10693])).

cnf(c_19001,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_18993,c_10701])).

cnf(c_2,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_7219,plain,
    ( k7_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_setfam_1(k2_tarski(X6,X7))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),X6),X7)
    | v1_funct_2(X5,X3,X1) != iProver_top
    | v1_funct_2(X4,X2,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6797,c_1501])).

cnf(c_13226,plain,
    ( k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),k1_setfam_1(k2_tarski(X3,X4))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3),X4)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_7219])).

cnf(c_13609,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),k1_setfam_1(k2_tarski(X3,X4))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3),X4)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13226,c_39,c_40,c_45,c_46])).

cnf(c_13610,plain,
    ( k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),k1_setfam_1(k2_tarski(X3,X4))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3),X4)
    | v1_funct_2(X2,X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_13609])).

cnf(c_13624,plain,
    ( k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1),X2)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_13610])).

cnf(c_13691,plain,
    ( k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1),X2)
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13624,c_40,c_45,c_46])).

cnf(c_13699,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0),X1) ),
    inference(superposition,[status(thm)],[c_1477,c_13691])).

cnf(c_13877,plain,
    ( k7_relat_1(k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0),k1_xboole_0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_13699])).

cnf(c_22854,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_19001,c_13877])).

cnf(c_23216,plain,
    ( k7_relat_1(k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0),k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_22854,c_13877])).

cnf(c_27495,plain,
    ( k4_subset_1(sK1,sK3,sK3) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22368,c_23216])).

cnf(c_27498,plain,
    ( k4_subset_1(sK1,sK3,sK3) = k1_xboole_0
    | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27495,c_6])).

cnf(c_21289,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0
    | r1_xboole_0(X0,k4_subset_1(sK1,sK3,sK3)) != iProver_top
    | v1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21037,c_1500])).

cnf(c_38,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2429,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK5,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | m1_subset_1(k1_tmap_1(X3,X1,X2,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X0),X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3) ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_2972,plain,
    ( ~ v1_funct_2(sK5,X0,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k1_tmap_1(X1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,sK3,X0),sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_3263,plain,
    ( ~ v1_funct_2(sK5,X0,sK2)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
    | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X0),sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2972])).

cnf(c_3264,plain,
    ( v1_funct_2(sK5,X0,sK2) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X0),sK2))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3263])).

cnf(c_3266,plain,
    ( v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK3),sK2))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_4745,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X0),sK2)))
    | v1_relat_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4746,plain,
    ( m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X0),sK2))) != iProver_top
    | v1_relat_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4745])).

cnf(c_4748,plain,
    ( m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK3),sK2))) != iProver_top
    | v1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4746])).

cnf(c_24575,plain,
    ( r1_xboole_0(X0,k4_subset_1(sK1,sK3,sK3)) != iProver_top
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21289,c_38,c_39,c_40,c_41,c_45,c_46,c_47,c_3266,c_4748])).

cnf(c_24576,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0
    | r1_xboole_0(X0,k4_subset_1(sK1,sK3,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_24575])).

cnf(c_27540,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0
    | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27498,c_24576])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1901,plain,
    ( r1_xboole_0(X0,k1_xboole_0)
    | k1_setfam_1(k2_tarski(X0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1902,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) != k1_xboole_0
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1901])).

cnf(c_27778,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27540,c_2,c_1902])).

cnf(c_27779,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0
    | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_27778])).

cnf(c_27797,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27779,c_22854])).

cnf(c_5125,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK3),sK4) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4004,c_3075])).

cnf(c_29905,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK3),sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27797,c_5125])).

cnf(c_24,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3185,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK4,sK2,sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k2_partfun1(sK3,sK2,sK5,k1_setfam_1(k2_tarski(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_2987,c_24])).

cnf(c_4212,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4004,c_3185])).

cnf(c_5061,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5057,c_4212])).

cnf(c_5238,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5061,c_5063])).

cnf(c_8116,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7344,c_5238])).

cnf(c_10381,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5057,c_10368])).

cnf(c_11019,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10381,c_42,c_48,c_49,c_50])).

cnf(c_11029,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_11019])).

cnf(c_11030,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11029,c_4004,c_7344])).

cnf(c_11031,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11030,c_2987,c_3075])).

cnf(c_11032,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11031,c_5125])).

cnf(c_11033,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11032])).

cnf(c_11730,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8116,c_34,c_32,c_11033])).

cnf(c_18425,plain,
    ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18421,c_11730])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43264,c_29905,c_27797,c_18425,c_50,c_49,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:37:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.04/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.04/2.48  
% 15.04/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.04/2.48  
% 15.04/2.48  ------  iProver source info
% 15.04/2.48  
% 15.04/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.04/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.04/2.48  git: non_committed_changes: false
% 15.04/2.48  git: last_make_outside_of_git: false
% 15.04/2.48  
% 15.04/2.48  ------ 
% 15.04/2.48  ------ Parsing...
% 15.04/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.04/2.48  
% 15.04/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.04/2.48  
% 15.04/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.04/2.48  
% 15.04/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.04/2.48  ------ Proving...
% 15.04/2.48  ------ Problem Properties 
% 15.04/2.48  
% 15.04/2.48  
% 15.04/2.48  clauses                                 37
% 15.04/2.48  conjectures                             14
% 15.04/2.48  EPR                                     11
% 15.04/2.48  Horn                                    27
% 15.04/2.48  unary                                   15
% 15.04/2.48  binary                                  7
% 15.04/2.48  lits                                    145
% 15.04/2.48  lits eq                                 19
% 15.04/2.48  fd_pure                                 0
% 15.04/2.48  fd_pseudo                               0
% 15.04/2.48  fd_cond                                 1
% 15.04/2.48  fd_pseudo_cond                          1
% 15.04/2.48  AC symbols                              0
% 15.04/2.48  
% 15.04/2.48  ------ Input Options Time Limit: Unbounded
% 15.04/2.48  
% 15.04/2.48  
% 15.04/2.48  ------ 
% 15.04/2.48  Current options:
% 15.04/2.48  ------ 
% 15.04/2.48  
% 15.04/2.48  
% 15.04/2.48  
% 15.04/2.48  
% 15.04/2.48  ------ Proving...
% 15.04/2.48  
% 15.04/2.48  
% 15.04/2.48  % SZS status Theorem for theBenchmark.p
% 15.04/2.48  
% 15.04/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.04/2.48  
% 15.04/2.48  fof(f18,conjecture,(
% 15.04/2.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f19,negated_conjecture,(
% 15.04/2.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 15.04/2.48    inference(negated_conjecture,[],[f18])).
% 15.04/2.48  
% 15.04/2.48  fof(f41,plain,(
% 15.04/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.04/2.48    inference(ennf_transformation,[],[f19])).
% 15.04/2.48  
% 15.04/2.48  fof(f42,plain,(
% 15.04/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.04/2.48    inference(flattening,[],[f41])).
% 15.04/2.48  
% 15.04/2.48  fof(f55,plain,(
% 15.04/2.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 15.04/2.48    introduced(choice_axiom,[])).
% 15.04/2.48  
% 15.04/2.48  fof(f54,plain,(
% 15.04/2.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 15.04/2.48    introduced(choice_axiom,[])).
% 15.04/2.48  
% 15.04/2.48  fof(f53,plain,(
% 15.04/2.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 15.04/2.48    introduced(choice_axiom,[])).
% 15.04/2.48  
% 15.04/2.48  fof(f52,plain,(
% 15.04/2.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 15.04/2.48    introduced(choice_axiom,[])).
% 15.04/2.48  
% 15.04/2.48  fof(f51,plain,(
% 15.04/2.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 15.04/2.48    introduced(choice_axiom,[])).
% 15.04/2.48  
% 15.04/2.48  fof(f50,plain,(
% 15.04/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 15.04/2.48    introduced(choice_axiom,[])).
% 15.04/2.48  
% 15.04/2.48  fof(f56,plain,(
% 15.04/2.48    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 15.04/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f55,f54,f53,f52,f51,f50])).
% 15.04/2.48  
% 15.04/2.48  fof(f94,plain,(
% 15.04/2.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f15,axiom,(
% 15.04/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f35,plain,(
% 15.04/2.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.04/2.48    inference(ennf_transformation,[],[f15])).
% 15.04/2.48  
% 15.04/2.48  fof(f36,plain,(
% 15.04/2.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.04/2.48    inference(flattening,[],[f35])).
% 15.04/2.48  
% 15.04/2.48  fof(f75,plain,(
% 15.04/2.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f36])).
% 15.04/2.48  
% 15.04/2.48  fof(f92,plain,(
% 15.04/2.48    v1_funct_1(sK6)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f87,plain,(
% 15.04/2.48    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f3,axiom,(
% 15.04/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f22,plain,(
% 15.04/2.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.04/2.48    inference(ennf_transformation,[],[f3])).
% 15.04/2.48  
% 15.04/2.48  fof(f60,plain,(
% 15.04/2.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.04/2.48    inference(cnf_transformation,[],[f22])).
% 15.04/2.48  
% 15.04/2.48  fof(f5,axiom,(
% 15.04/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f62,plain,(
% 15.04/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.04/2.48    inference(cnf_transformation,[],[f5])).
% 15.04/2.48  
% 15.04/2.48  fof(f99,plain,(
% 15.04/2.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.04/2.48    inference(definition_unfolding,[],[f60,f62])).
% 15.04/2.48  
% 15.04/2.48  fof(f91,plain,(
% 15.04/2.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f89,plain,(
% 15.04/2.48    v1_funct_1(sK5)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f16,axiom,(
% 15.04/2.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f37,plain,(
% 15.04/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 15.04/2.48    inference(ennf_transformation,[],[f16])).
% 15.04/2.48  
% 15.04/2.48  fof(f38,plain,(
% 15.04/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 15.04/2.48    inference(flattening,[],[f37])).
% 15.04/2.48  
% 15.04/2.48  fof(f48,plain,(
% 15.04/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 15.04/2.48    inference(nnf_transformation,[],[f38])).
% 15.04/2.48  
% 15.04/2.48  fof(f49,plain,(
% 15.04/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 15.04/2.48    inference(flattening,[],[f48])).
% 15.04/2.48  
% 15.04/2.48  fof(f76,plain,(
% 15.04/2.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f49])).
% 15.04/2.48  
% 15.04/2.48  fof(f105,plain,(
% 15.04/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.04/2.48    inference(equality_resolution,[],[f76])).
% 15.04/2.48  
% 15.04/2.48  fof(f17,axiom,(
% 15.04/2.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f39,plain,(
% 15.04/2.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 15.04/2.48    inference(ennf_transformation,[],[f17])).
% 15.04/2.48  
% 15.04/2.48  fof(f40,plain,(
% 15.04/2.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.04/2.48    inference(flattening,[],[f39])).
% 15.04/2.48  
% 15.04/2.48  fof(f79,plain,(
% 15.04/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f40])).
% 15.04/2.48  
% 15.04/2.48  fof(f80,plain,(
% 15.04/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f40])).
% 15.04/2.48  
% 15.04/2.48  fof(f81,plain,(
% 15.04/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f40])).
% 15.04/2.48  
% 15.04/2.48  fof(f4,axiom,(
% 15.04/2.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f23,plain,(
% 15.04/2.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 15.04/2.48    inference(ennf_transformation,[],[f4])).
% 15.04/2.48  
% 15.04/2.48  fof(f61,plain,(
% 15.04/2.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f23])).
% 15.04/2.48  
% 15.04/2.48  fof(f83,plain,(
% 15.04/2.48    ~v1_xboole_0(sK2)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f84,plain,(
% 15.04/2.48    ~v1_xboole_0(sK3)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f90,plain,(
% 15.04/2.48    v1_funct_2(sK5,sK3,sK2)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f88,plain,(
% 15.04/2.48    r1_subset_1(sK3,sK4)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f9,axiom,(
% 15.04/2.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f26,plain,(
% 15.04/2.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 15.04/2.48    inference(ennf_transformation,[],[f9])).
% 15.04/2.48  
% 15.04/2.48  fof(f27,plain,(
% 15.04/2.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.04/2.48    inference(flattening,[],[f26])).
% 15.04/2.48  
% 15.04/2.48  fof(f44,plain,(
% 15.04/2.48    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.04/2.48    inference(nnf_transformation,[],[f27])).
% 15.04/2.48  
% 15.04/2.48  fof(f66,plain,(
% 15.04/2.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f44])).
% 15.04/2.48  
% 15.04/2.48  fof(f86,plain,(
% 15.04/2.48    ~v1_xboole_0(sK4)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f1,axiom,(
% 15.04/2.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f43,plain,(
% 15.04/2.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.04/2.48    inference(nnf_transformation,[],[f1])).
% 15.04/2.48  
% 15.04/2.48  fof(f57,plain,(
% 15.04/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f43])).
% 15.04/2.48  
% 15.04/2.48  fof(f97,plain,(
% 15.04/2.48    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 15.04/2.48    inference(definition_unfolding,[],[f57,f62])).
% 15.04/2.48  
% 15.04/2.48  fof(f10,axiom,(
% 15.04/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f28,plain,(
% 15.04/2.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.04/2.48    inference(ennf_transformation,[],[f10])).
% 15.04/2.48  
% 15.04/2.48  fof(f68,plain,(
% 15.04/2.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.04/2.48    inference(cnf_transformation,[],[f28])).
% 15.04/2.48  
% 15.04/2.48  fof(f6,axiom,(
% 15.04/2.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f24,plain,(
% 15.04/2.48    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 15.04/2.48    inference(ennf_transformation,[],[f6])).
% 15.04/2.48  
% 15.04/2.48  fof(f63,plain,(
% 15.04/2.48    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f24])).
% 15.04/2.48  
% 15.04/2.48  fof(f100,plain,(
% 15.04/2.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 15.04/2.48    inference(definition_unfolding,[],[f63,f62])).
% 15.04/2.48  
% 15.04/2.48  fof(f85,plain,(
% 15.04/2.48    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f13,axiom,(
% 15.04/2.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f31,plain,(
% 15.04/2.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 15.04/2.48    inference(ennf_transformation,[],[f13])).
% 15.04/2.48  
% 15.04/2.48  fof(f32,plain,(
% 15.04/2.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 15.04/2.48    inference(flattening,[],[f31])).
% 15.04/2.48  
% 15.04/2.48  fof(f72,plain,(
% 15.04/2.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f32])).
% 15.04/2.48  
% 15.04/2.48  fof(f93,plain,(
% 15.04/2.48    v1_funct_2(sK6,sK4,sK2)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f14,axiom,(
% 15.04/2.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f33,plain,(
% 15.04/2.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.04/2.48    inference(ennf_transformation,[],[f14])).
% 15.04/2.48  
% 15.04/2.48  fof(f34,plain,(
% 15.04/2.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.04/2.48    inference(flattening,[],[f33])).
% 15.04/2.48  
% 15.04/2.48  fof(f47,plain,(
% 15.04/2.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.04/2.48    inference(nnf_transformation,[],[f34])).
% 15.04/2.48  
% 15.04/2.48  fof(f73,plain,(
% 15.04/2.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f47])).
% 15.04/2.48  
% 15.04/2.48  fof(f11,axiom,(
% 15.04/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f21,plain,(
% 15.04/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 15.04/2.48    inference(pure_predicate_removal,[],[f11])).
% 15.04/2.48  
% 15.04/2.48  fof(f29,plain,(
% 15.04/2.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.04/2.48    inference(ennf_transformation,[],[f21])).
% 15.04/2.48  
% 15.04/2.48  fof(f69,plain,(
% 15.04/2.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.04/2.48    inference(cnf_transformation,[],[f29])).
% 15.04/2.48  
% 15.04/2.48  fof(f8,axiom,(
% 15.04/2.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f25,plain,(
% 15.04/2.48    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 15.04/2.48    inference(ennf_transformation,[],[f8])).
% 15.04/2.48  
% 15.04/2.48  fof(f65,plain,(
% 15.04/2.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f25])).
% 15.04/2.48  
% 15.04/2.48  fof(f7,axiom,(
% 15.04/2.48    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f64,plain,(
% 15.04/2.48    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f7])).
% 15.04/2.48  
% 15.04/2.48  fof(f82,plain,(
% 15.04/2.48    ~v1_xboole_0(sK1)),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  fof(f12,axiom,(
% 15.04/2.48    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f20,plain,(
% 15.04/2.48    ! [X0] : ~(! [X1] : ~r1_xboole_0(X1,X0) & k1_xboole_0 != X0)),
% 15.04/2.48    inference(pure_predicate_removal,[],[f12])).
% 15.04/2.48  
% 15.04/2.48  fof(f30,plain,(
% 15.04/2.48    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) | k1_xboole_0 = X0)),
% 15.04/2.48    inference(ennf_transformation,[],[f20])).
% 15.04/2.48  
% 15.04/2.48  fof(f45,plain,(
% 15.04/2.48    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) => r1_xboole_0(sK0(X0),X0))),
% 15.04/2.48    introduced(choice_axiom,[])).
% 15.04/2.48  
% 15.04/2.48  fof(f46,plain,(
% 15.04/2.48    ! [X0] : (r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0)),
% 15.04/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f45])).
% 15.04/2.48  
% 15.04/2.48  fof(f70,plain,(
% 15.04/2.48    ( ! [X0] : (r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 15.04/2.48    inference(cnf_transformation,[],[f46])).
% 15.04/2.48  
% 15.04/2.48  fof(f77,plain,(
% 15.04/2.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.04/2.48    inference(cnf_transformation,[],[f49])).
% 15.04/2.48  
% 15.04/2.48  fof(f104,plain,(
% 15.04/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.04/2.48    inference(equality_resolution,[],[f77])).
% 15.04/2.48  
% 15.04/2.48  fof(f2,axiom,(
% 15.04/2.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.04/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.04/2.48  
% 15.04/2.48  fof(f59,plain,(
% 15.04/2.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.04/2.48    inference(cnf_transformation,[],[f2])).
% 15.04/2.48  
% 15.04/2.48  fof(f98,plain,(
% 15.04/2.48    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 15.04/2.48    inference(definition_unfolding,[],[f59,f62])).
% 15.04/2.48  
% 15.04/2.48  fof(f58,plain,(
% 15.04/2.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.04/2.48    inference(cnf_transformation,[],[f43])).
% 15.04/2.48  
% 15.04/2.48  fof(f96,plain,(
% 15.04/2.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.04/2.48    inference(definition_unfolding,[],[f58,f62])).
% 15.04/2.48  
% 15.04/2.48  fof(f95,plain,(
% 15.04/2.48    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 15.04/2.48    inference(cnf_transformation,[],[f56])).
% 15.04/2.48  
% 15.04/2.48  cnf(c_25,negated_conjecture,
% 15.04/2.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 15.04/2.48      inference(cnf_transformation,[],[f94]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1486,plain,
% 15.04/2.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_17,plain,
% 15.04/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | ~ v1_funct_1(X0)
% 15.04/2.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 15.04/2.48      inference(cnf_transformation,[],[f75]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1491,plain,
% 15.04/2.48      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 15.04/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.04/2.48      | v1_funct_1(X2) != iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_4781,plain,
% 15.04/2.48      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 15.04/2.48      | v1_funct_1(sK6) != iProver_top ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_1486,c_1491]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_27,negated_conjecture,
% 15.04/2.48      ( v1_funct_1(sK6) ),
% 15.04/2.48      inference(cnf_transformation,[],[f92]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2038,plain,
% 15.04/2.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.04/2.48      | ~ v1_funct_1(sK6)
% 15.04/2.48      | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
% 15.04/2.48      inference(instantiation,[status(thm)],[c_17]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2322,plain,
% 15.04/2.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 15.04/2.48      | ~ v1_funct_1(sK6)
% 15.04/2.48      | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 15.04/2.48      inference(instantiation,[status(thm)],[c_2038]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_5057,plain,
% 15.04/2.48      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 15.04/2.48      inference(global_propositional_subsumption,
% 15.04/2.48                [status(thm)],
% 15.04/2.48                [c_4781,c_27,c_25,c_2322]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_32,negated_conjecture,
% 15.04/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 15.04/2.48      inference(cnf_transformation,[],[f87]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1479,plain,
% 15.04/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_3,plain,
% 15.04/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.04/2.48      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 15.04/2.48      inference(cnf_transformation,[],[f99]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1503,plain,
% 15.04/2.48      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 15.04/2.48      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2987,plain,
% 15.04/2.48      ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_1479,c_1503]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_28,negated_conjecture,
% 15.04/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 15.04/2.48      inference(cnf_transformation,[],[f91]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1483,plain,
% 15.04/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_4782,plain,
% 15.04/2.48      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 15.04/2.48      | v1_funct_1(sK5) != iProver_top ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_1483,c_1491]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_30,negated_conjecture,
% 15.04/2.48      ( v1_funct_1(sK5) ),
% 15.04/2.48      inference(cnf_transformation,[],[f89]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2043,plain,
% 15.04/2.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.04/2.48      | ~ v1_funct_1(sK5)
% 15.04/2.48      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 15.04/2.48      inference(instantiation,[status(thm)],[c_17]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2327,plain,
% 15.04/2.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.48      | ~ v1_funct_1(sK5)
% 15.04/2.48      | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 15.04/2.48      inference(instantiation,[status(thm)],[c_2043]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_5063,plain,
% 15.04/2.48      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 15.04/2.48      inference(global_propositional_subsumption,
% 15.04/2.48                [status(thm)],
% 15.04/2.48                [c_4782,c_30,c_28,c_2327]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_20,plain,
% 15.04/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.48      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 15.04/2.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 15.04/2.48      | ~ v1_funct_1(X0)
% 15.04/2.48      | ~ v1_funct_1(X3)
% 15.04/2.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 15.04/2.48      | v1_xboole_0(X5)
% 15.04/2.48      | v1_xboole_0(X2)
% 15.04/2.48      | v1_xboole_0(X4)
% 15.04/2.48      | v1_xboole_0(X1)
% 15.04/2.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.04/2.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 15.04/2.48      inference(cnf_transformation,[],[f105]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_23,plain,
% 15.04/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.48      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.48      | ~ v1_funct_1(X0)
% 15.04/2.48      | ~ v1_funct_1(X3)
% 15.04/2.48      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 15.04/2.48      | v1_xboole_0(X5)
% 15.04/2.48      | v1_xboole_0(X2)
% 15.04/2.48      | v1_xboole_0(X4)
% 15.04/2.48      | v1_xboole_0(X1) ),
% 15.04/2.48      inference(cnf_transformation,[],[f79]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_22,plain,
% 15.04/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.48      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.48      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 15.04/2.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.48      | ~ v1_funct_1(X0)
% 15.04/2.48      | ~ v1_funct_1(X3)
% 15.04/2.48      | v1_xboole_0(X5)
% 15.04/2.48      | v1_xboole_0(X2)
% 15.04/2.48      | v1_xboole_0(X4)
% 15.04/2.48      | v1_xboole_0(X1) ),
% 15.04/2.48      inference(cnf_transformation,[],[f80]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_21,plain,
% 15.04/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.48      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.48      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 15.04/2.48      | ~ v1_funct_1(X0)
% 15.04/2.48      | ~ v1_funct_1(X3)
% 15.04/2.48      | v1_xboole_0(X5)
% 15.04/2.48      | v1_xboole_0(X2)
% 15.04/2.48      | v1_xboole_0(X4)
% 15.04/2.48      | v1_xboole_0(X1) ),
% 15.04/2.48      inference(cnf_transformation,[],[f81]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_371,plain,
% 15.04/2.48      ( ~ v1_funct_1(X3)
% 15.04/2.48      | ~ v1_funct_1(X0)
% 15.04/2.48      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.48      | ~ v1_funct_2(X0,X1,X2)
% 15.04/2.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.48      | v1_xboole_0(X5)
% 15.04/2.48      | v1_xboole_0(X2)
% 15.04/2.48      | v1_xboole_0(X4)
% 15.04/2.48      | v1_xboole_0(X1)
% 15.04/2.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.04/2.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 15.04/2.48      inference(global_propositional_subsumption,
% 15.04/2.48                [status(thm)],
% 15.04/2.48                [c_20,c_23,c_22,c_21]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_372,plain,
% 15.04/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.48      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.48      | ~ v1_funct_1(X0)
% 15.04/2.48      | ~ v1_funct_1(X3)
% 15.04/2.48      | v1_xboole_0(X1)
% 15.04/2.48      | v1_xboole_0(X2)
% 15.04/2.48      | v1_xboole_0(X4)
% 15.04/2.48      | v1_xboole_0(X5)
% 15.04/2.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.04/2.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 15.04/2.48      inference(renaming,[status(thm)],[c_371]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1473,plain,
% 15.04/2.48      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 15.04/2.48      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 15.04/2.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.04/2.48      | v1_funct_2(X5,X4,X1) != iProver_top
% 15.04/2.48      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 15.04/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.04/2.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 15.04/2.48      | v1_funct_1(X2) != iProver_top
% 15.04/2.48      | v1_funct_1(X5) != iProver_top
% 15.04/2.48      | v1_xboole_0(X3) = iProver_top
% 15.04/2.48      | v1_xboole_0(X1) = iProver_top
% 15.04/2.48      | v1_xboole_0(X4) = iProver_top
% 15.04/2.48      | v1_xboole_0(X0) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_4,plain,
% 15.04/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.04/2.48      | ~ v1_xboole_0(X1)
% 15.04/2.48      | v1_xboole_0(X0) ),
% 15.04/2.48      inference(cnf_transformation,[],[f61]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1502,plain,
% 15.04/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.04/2.48      | v1_xboole_0(X1) != iProver_top
% 15.04/2.48      | v1_xboole_0(X0) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1748,plain,
% 15.04/2.48      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 15.04/2.48      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
% 15.04/2.48      | v1_funct_2(X5,X4,X1) != iProver_top
% 15.04/2.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 15.04/2.48      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 15.04/2.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 15.04/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.04/2.48      | v1_funct_1(X5) != iProver_top
% 15.04/2.48      | v1_funct_1(X2) != iProver_top
% 15.04/2.48      | v1_xboole_0(X0) = iProver_top
% 15.04/2.48      | v1_xboole_0(X1) = iProver_top
% 15.04/2.48      | v1_xboole_0(X4) = iProver_top ),
% 15.04/2.48      inference(forward_subsumption_resolution,
% 15.04/2.48                [status(thm)],
% 15.04/2.48                [c_1473,c_1502]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_9374,plain,
% 15.04/2.48      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 15.04/2.48      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 15.04/2.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 15.04/2.48      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 15.04/2.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 15.04/2.48      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.48      | v1_funct_1(X1) != iProver_top
% 15.04/2.48      | v1_funct_1(sK5) != iProver_top
% 15.04/2.48      | v1_xboole_0(X0) = iProver_top
% 15.04/2.48      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.48      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_5063,c_1748]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_36,negated_conjecture,
% 15.04/2.48      ( ~ v1_xboole_0(sK2) ),
% 15.04/2.48      inference(cnf_transformation,[],[f83]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_39,plain,
% 15.04/2.48      ( v1_xboole_0(sK2) != iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_35,negated_conjecture,
% 15.04/2.48      ( ~ v1_xboole_0(sK3) ),
% 15.04/2.48      inference(cnf_transformation,[],[f84]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_40,plain,
% 15.04/2.48      ( v1_xboole_0(sK3) != iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_45,plain,
% 15.04/2.48      ( v1_funct_1(sK5) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_29,negated_conjecture,
% 15.04/2.48      ( v1_funct_2(sK5,sK3,sK2) ),
% 15.04/2.48      inference(cnf_transformation,[],[f90]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_46,plain,
% 15.04/2.48      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_47,plain,
% 15.04/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_32387,plain,
% 15.04/2.48      ( v1_funct_1(X1) != iProver_top
% 15.04/2.48      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 15.04/2.48      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 15.04/2.48      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 15.04/2.48      | v1_xboole_0(X0) = iProver_top ),
% 15.04/2.48      inference(global_propositional_subsumption,
% 15.04/2.48                [status(thm)],
% 15.04/2.48                [c_9374,c_39,c_40,c_45,c_46,c_47]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_32388,plain,
% 15.04/2.48      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 15.04/2.48      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 15.04/2.48      | v1_funct_2(X1,X0,sK2) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 15.04/2.48      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.48      | v1_funct_1(X1) != iProver_top
% 15.04/2.48      | v1_xboole_0(X0) = iProver_top ),
% 15.04/2.48      inference(renaming,[status(thm)],[c_32387]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_32409,plain,
% 15.04/2.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5
% 15.04/2.48      | k2_partfun1(sK4,sK2,X0,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 15.04/2.48      | v1_funct_2(X0,sK4,sK2) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.48      | v1_funct_1(X0) != iProver_top
% 15.04/2.48      | v1_xboole_0(sK4) = iProver_top ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_2987,c_32388]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_31,negated_conjecture,
% 15.04/2.48      ( r1_subset_1(sK3,sK4) ),
% 15.04/2.48      inference(cnf_transformation,[],[f88]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1480,plain,
% 15.04/2.48      ( r1_subset_1(sK3,sK4) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_9,plain,
% 15.04/2.48      ( ~ r1_subset_1(X0,X1)
% 15.04/2.48      | r1_xboole_0(X0,X1)
% 15.04/2.48      | v1_xboole_0(X0)
% 15.04/2.48      | v1_xboole_0(X1) ),
% 15.04/2.48      inference(cnf_transformation,[],[f66]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1498,plain,
% 15.04/2.48      ( r1_subset_1(X0,X1) != iProver_top
% 15.04/2.48      | r1_xboole_0(X0,X1) = iProver_top
% 15.04/2.48      | v1_xboole_0(X1) = iProver_top
% 15.04/2.48      | v1_xboole_0(X0) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_3515,plain,
% 15.04/2.48      ( r1_xboole_0(sK3,sK4) = iProver_top
% 15.04/2.48      | v1_xboole_0(sK4) = iProver_top
% 15.04/2.48      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_1480,c_1498]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_33,negated_conjecture,
% 15.04/2.48      ( ~ v1_xboole_0(sK4) ),
% 15.04/2.48      inference(cnf_transformation,[],[f86]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_42,plain,
% 15.04/2.48      ( v1_xboole_0(sK4) != iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_44,plain,
% 15.04/2.48      ( r1_subset_1(sK3,sK4) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1944,plain,
% 15.04/2.48      ( ~ r1_subset_1(sK3,sK4)
% 15.04/2.48      | r1_xboole_0(sK3,sK4)
% 15.04/2.48      | v1_xboole_0(sK4)
% 15.04/2.48      | v1_xboole_0(sK3) ),
% 15.04/2.48      inference(instantiation,[status(thm)],[c_9]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1945,plain,
% 15.04/2.48      ( r1_subset_1(sK3,sK4) != iProver_top
% 15.04/2.48      | r1_xboole_0(sK3,sK4) = iProver_top
% 15.04/2.48      | v1_xboole_0(sK4) = iProver_top
% 15.04/2.48      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_3998,plain,
% 15.04/2.48      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 15.04/2.48      inference(global_propositional_subsumption,
% 15.04/2.48                [status(thm)],
% 15.04/2.48                [c_3515,c_40,c_42,c_44,c_1945]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1,plain,
% 15.04/2.48      ( ~ r1_xboole_0(X0,X1)
% 15.04/2.48      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 15.04/2.48      inference(cnf_transformation,[],[f97]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1504,plain,
% 15.04/2.48      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 15.04/2.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_4004,plain,
% 15.04/2.48      ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_3998,c_1504]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_32506,plain,
% 15.04/2.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5
% 15.04/2.48      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,X0,k1_xboole_0)
% 15.04/2.48      | v1_funct_2(X0,sK4,sK2) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.48      | v1_funct_1(X0) != iProver_top
% 15.04/2.48      | v1_xboole_0(sK4) = iProver_top ),
% 15.04/2.48      inference(light_normalisation,[status(thm)],[c_32409,c_4004]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_10,plain,
% 15.04/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | v1_relat_1(X0) ),
% 15.04/2.48      inference(cnf_transformation,[],[f68]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1497,plain,
% 15.04/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.48      | v1_relat_1(X0) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2680,plain,
% 15.04/2.48      ( v1_relat_1(sK5) = iProver_top ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_1483,c_1497]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_5,plain,
% 15.04/2.48      ( ~ v1_relat_1(X0)
% 15.04/2.48      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 15.04/2.48      inference(cnf_transformation,[],[f100]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1501,plain,
% 15.04/2.48      ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 15.04/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_3075,plain,
% 15.04/2.48      ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK5,X0),X1) ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_2680,c_1501]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_32507,plain,
% 15.04/2.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5
% 15.04/2.48      | k2_partfun1(sK4,sK2,X0,k1_xboole_0) != k7_relat_1(k7_relat_1(sK5,sK3),sK4)
% 15.04/2.48      | v1_funct_2(X0,sK4,sK2) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.48      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.48      | v1_funct_1(X0) != iProver_top
% 15.04/2.48      | v1_xboole_0(sK4) = iProver_top ),
% 15.04/2.48      inference(demodulation,[status(thm)],[c_32506,c_2987,c_3075]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_34,negated_conjecture,
% 15.04/2.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 15.04/2.48      inference(cnf_transformation,[],[f85]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_41,plain,
% 15.04/2.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_43,plain,
% 15.04/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_43251,plain,
% 15.04/2.48      ( v1_funct_1(X0) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.48      | v1_funct_2(X0,sK4,sK2) != iProver_top
% 15.04/2.48      | k2_partfun1(sK4,sK2,X0,k1_xboole_0) != k7_relat_1(k7_relat_1(sK5,sK3),sK4)
% 15.04/2.48      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5 ),
% 15.04/2.48      inference(global_propositional_subsumption,
% 15.04/2.48                [status(thm)],
% 15.04/2.48                [c_32507,c_41,c_42,c_43]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_43252,plain,
% 15.04/2.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,X0),sK3) = sK5
% 15.04/2.48      | k2_partfun1(sK4,sK2,X0,k1_xboole_0) != k7_relat_1(k7_relat_1(sK5,sK3),sK4)
% 15.04/2.48      | v1_funct_2(X0,sK4,sK2) != iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.48      | v1_funct_1(X0) != iProver_top ),
% 15.04/2.48      inference(renaming,[status(thm)],[c_43251]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_43262,plain,
% 15.04/2.48      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 15.04/2.48      | k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k7_relat_1(sK6,k1_xboole_0)
% 15.04/2.48      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 15.04/2.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.48      | v1_funct_1(sK6) != iProver_top ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_5057,c_43252]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_13,plain,
% 15.04/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.48      | v1_partfun1(X0,X1)
% 15.04/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.48      | ~ v1_funct_1(X0)
% 15.04/2.48      | v1_xboole_0(X2) ),
% 15.04/2.48      inference(cnf_transformation,[],[f72]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_1494,plain,
% 15.04/2.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.48      | v1_partfun1(X0,X1) = iProver_top
% 15.04/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.48      | v1_funct_1(X0) != iProver_top
% 15.04/2.48      | v1_xboole_0(X2) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2799,plain,
% 15.04/2.48      ( v1_funct_2(sK6,sK4,sK2) != iProver_top
% 15.04/2.48      | v1_partfun1(sK6,sK4) = iProver_top
% 15.04/2.48      | v1_funct_1(sK6) != iProver_top
% 15.04/2.48      | v1_xboole_0(sK2) = iProver_top ),
% 15.04/2.48      inference(superposition,[status(thm)],[c_1486,c_1494]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_48,plain,
% 15.04/2.48      ( v1_funct_1(sK6) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_26,negated_conjecture,
% 15.04/2.48      ( v1_funct_2(sK6,sK4,sK2) ),
% 15.04/2.48      inference(cnf_transformation,[],[f93]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_49,plain,
% 15.04/2.48      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_50,plain,
% 15.04/2.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2028,plain,
% 15.04/2.48      ( ~ v1_funct_2(sK6,X0,X1)
% 15.04/2.48      | v1_partfun1(sK6,X0)
% 15.04/2.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.04/2.48      | ~ v1_funct_1(sK6)
% 15.04/2.48      | v1_xboole_0(X1) ),
% 15.04/2.48      inference(instantiation,[status(thm)],[c_13]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2316,plain,
% 15.04/2.48      ( ~ v1_funct_2(sK6,sK4,sK2)
% 15.04/2.48      | v1_partfun1(sK6,sK4)
% 15.04/2.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 15.04/2.48      | ~ v1_funct_1(sK6)
% 15.04/2.48      | v1_xboole_0(sK2) ),
% 15.04/2.48      inference(instantiation,[status(thm)],[c_2028]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_2317,plain,
% 15.04/2.48      ( v1_funct_2(sK6,sK4,sK2) != iProver_top
% 15.04/2.48      | v1_partfun1(sK6,sK4) = iProver_top
% 15.04/2.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.48      | v1_funct_1(sK6) != iProver_top
% 15.04/2.48      | v1_xboole_0(sK2) = iProver_top ),
% 15.04/2.48      inference(predicate_to_equality,[status(thm)],[c_2316]) ).
% 15.04/2.48  
% 15.04/2.48  cnf(c_4087,plain,
% 15.04/2.48      ( v1_partfun1(sK6,sK4) = iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_2799,c_39,c_48,c_49,c_50,c_2317]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_16,plain,
% 15.04/2.49      ( ~ v1_partfun1(X0,X1)
% 15.04/2.49      | ~ v4_relat_1(X0,X1)
% 15.04/2.49      | ~ v1_relat_1(X0)
% 15.04/2.49      | k1_relat_1(X0) = X1 ),
% 15.04/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1492,plain,
% 15.04/2.49      ( k1_relat_1(X0) = X1
% 15.04/2.49      | v1_partfun1(X0,X1) != iProver_top
% 15.04/2.49      | v4_relat_1(X0,X1) != iProver_top
% 15.04/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_4549,plain,
% 15.04/2.49      ( k1_relat_1(sK6) = sK4
% 15.04/2.49      | v4_relat_1(sK6,sK4) != iProver_top
% 15.04/2.49      | v1_relat_1(sK6) != iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_4087,c_1492]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1922,plain,
% 15.04/2.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 15.04/2.49      | v1_relat_1(sK6) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_11,plain,
% 15.04/2.49      ( v4_relat_1(X0,X1)
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.04/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1928,plain,
% 15.04/2.49      ( v4_relat_1(sK6,sK4)
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_11]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2121,plain,
% 15.04/2.49      ( ~ v1_partfun1(sK6,X0)
% 15.04/2.49      | ~ v4_relat_1(sK6,X0)
% 15.04/2.49      | ~ v1_relat_1(sK6)
% 15.04/2.49      | k1_relat_1(sK6) = X0 ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_16]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2872,plain,
% 15.04/2.49      ( ~ v1_partfun1(sK6,sK4)
% 15.04/2.49      | ~ v4_relat_1(sK6,sK4)
% 15.04/2.49      | ~ v1_relat_1(sK6)
% 15.04/2.49      | k1_relat_1(sK6) = sK4 ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2121]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_5220,plain,
% 15.04/2.49      ( k1_relat_1(sK6) = sK4 ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_4549,c_36,c_27,c_26,c_25,c_1922,c_1928,c_2316,c_2872]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7,plain,
% 15.04/2.49      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 15.04/2.49      | ~ v1_relat_1(X1)
% 15.04/2.49      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 15.04/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1500,plain,
% 15.04/2.49      ( k7_relat_1(X0,X1) = k1_xboole_0
% 15.04/2.49      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 15.04/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_5224,plain,
% 15.04/2.49      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 15.04/2.49      | r1_xboole_0(X0,sK4) != iProver_top
% 15.04/2.49      | v1_relat_1(sK6) != iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_5220,c_1500]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1923,plain,
% 15.04/2.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.49      | v1_relat_1(sK6) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_1922]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7077,plain,
% 15.04/2.49      ( r1_xboole_0(X0,sK4) != iProver_top
% 15.04/2.49      | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_5224,c_50,c_1923]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7078,plain,
% 15.04/2.49      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 15.04/2.49      | r1_xboole_0(X0,sK4) != iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_7077]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7086,plain,
% 15.04/2.49      ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_3998,c_7078]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2679,plain,
% 15.04/2.49      ( v1_relat_1(sK6) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1486,c_1497]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_3004,plain,
% 15.04/2.49      ( k7_relat_1(sK6,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK6,X0),X1) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_2679,c_1501]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_4283,plain,
% 15.04/2.49      ( k7_relat_1(k7_relat_1(sK6,sK3),sK4) = k7_relat_1(sK6,k1_xboole_0) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_4004,c_3004]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7343,plain,
% 15.04/2.49      ( k7_relat_1(k1_xboole_0,sK4) = k7_relat_1(sK6,k1_xboole_0) ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_7086,c_4283]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_6,plain,
% 15.04/2.49      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.04/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7344,plain,
% 15.04/2.49      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_7343,c_6]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_43263,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 15.04/2.49      | k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k1_xboole_0
% 15.04/2.49      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.49      | v1_funct_1(sK6) != iProver_top ),
% 15.04/2.49      inference(light_normalisation,[status(thm)],[c_43262,c_7344]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1489,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_xboole_0(X5) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1693,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(forward_subsumption_resolution,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_1489,c_1502]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_6794,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 15.04/2.49      | v1_funct_2(X5,X2,X3) != iProver_top
% 15.04/2.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 15.04/2.49      | v1_funct_1(X5) != iProver_top
% 15.04/2.49      | v1_funct_1(X4) != iProver_top
% 15.04/2.49      | v1_funct_1(k1_tmap_1(X0,X3,X1,X2,X4,X5)) != iProver_top
% 15.04/2.49      | v1_xboole_0(X3) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1693,c_1491]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1487,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 15.04/2.49      | v1_xboole_0(X5) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1641,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(forward_subsumption_resolution,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_1487,c_1502]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_17188,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 15.04/2.49      | v1_funct_2(X5,X2,X3) != iProver_top
% 15.04/2.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 15.04/2.49      | v1_funct_1(X5) != iProver_top
% 15.04/2.49      | v1_funct_1(X4) != iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(X3) = iProver_top ),
% 15.04/2.49      inference(forward_subsumption_resolution,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_6794,c_1641]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_17193,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_funct_1(sK6) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK4) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1486,c_17188]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_17576,plain,
% 15.04/2.49      ( v1_funct_1(X2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_17193,c_39,c_42,c_48,c_49]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_17577,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,X1,sK4),sK2,k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK4,X2,sK6),X3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_17576]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_17591,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_17577]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18331,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),X1)
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_17591,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18340,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0)
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1479,c_18331]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_37,negated_conjecture,
% 15.04/2.49      ( ~ v1_xboole_0(sK1) ),
% 15.04/2.49      inference(cnf_transformation,[],[f82]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2063,plain,
% 15.04/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.49      | ~ v1_funct_2(sK5,X3,X2)
% 15.04/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 15.04/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 15.04/2.49      | ~ v1_funct_1(X0)
% 15.04/2.49      | v1_funct_1(k1_tmap_1(X4,X2,X3,X1,sK5,X0))
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(X2)
% 15.04/2.49      | v1_xboole_0(X3)
% 15.04/2.49      | v1_xboole_0(X4) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_23]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2404,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK6,X0,X1)
% 15.04/2.49      | ~ v1_funct_2(sK5,X2,X1)
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 15.04/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.04/2.49      | v1_funct_1(k1_tmap_1(X3,X1,X2,X0,sK5,sK6))
% 15.04/2.49      | ~ v1_funct_1(sK6)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(X2)
% 15.04/2.49      | v1_xboole_0(X3) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2063]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2947,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK6,X0,sK2)
% 15.04/2.49      | ~ v1_funct_2(sK5,sK3,sK2)
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
% 15.04/2.49      | v1_funct_1(k1_tmap_1(X1,sK2,sK3,X0,sK5,sK6))
% 15.04/2.49      | ~ v1_funct_1(sK6)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(sK2)
% 15.04/2.49      | v1_xboole_0(sK3) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2404]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_3237,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK6,sK4,sK2)
% 15.04/2.49      | ~ v1_funct_2(sK5,sK3,sK2)
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 15.04/2.49      | v1_funct_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6))
% 15.04/2.49      | ~ v1_funct_1(sK6)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(sK2)
% 15.04/2.49      | v1_xboole_0(sK4)
% 15.04/2.49      | v1_xboole_0(sK3) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2947]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_4532,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK6,sK4,sK2)
% 15.04/2.49      | ~ v1_funct_2(sK5,sK3,sK2)
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 15.04/2.49      | v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
% 15.04/2.49      | ~ v1_funct_1(sK6)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(sK2)
% 15.04/2.49      | v1_xboole_0(sK4)
% 15.04/2.49      | v1_xboole_0(sK3)
% 15.04/2.49      | v1_xboole_0(sK1) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_3237]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2086,plain,
% 15.04/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.49      | ~ v1_funct_2(sK5,X3,X2)
% 15.04/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 15.04/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.49      | m1_subset_1(k1_tmap_1(X4,X2,X3,X1,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X3,X1),X2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 15.04/2.49      | ~ v1_funct_1(X0)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(X2)
% 15.04/2.49      | v1_xboole_0(X3)
% 15.04/2.49      | v1_xboole_0(X4) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_21]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2424,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK6,X0,X1)
% 15.04/2.49      | ~ v1_funct_2(sK5,X2,X1)
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 15.04/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 15.04/2.49      | m1_subset_1(k1_tmap_1(X3,X1,X2,X0,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X0),X1)))
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.04/2.49      | ~ v1_funct_1(sK6)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(X2)
% 15.04/2.49      | v1_xboole_0(X3) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2086]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2967,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK6,X0,sK2)
% 15.04/2.49      | ~ v1_funct_2(sK5,sK3,sK2)
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.04/2.49      | m1_subset_1(k1_tmap_1(X1,sK2,sK3,X0,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,sK3,X0),sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
% 15.04/2.49      | ~ v1_funct_1(sK6)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(sK2)
% 15.04/2.49      | v1_xboole_0(sK3) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2424]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_3258,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK6,sK4,sK2)
% 15.04/2.49      | ~ v1_funct_2(sK5,sK3,sK2)
% 15.04/2.49      | m1_subset_1(k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK3,sK4),sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 15.04/2.49      | ~ v1_funct_1(sK6)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(sK2)
% 15.04/2.49      | v1_xboole_0(sK4)
% 15.04/2.49      | v1_xboole_0(sK3) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2967]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_4725,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK6,sK4,sK2)
% 15.04/2.49      | ~ v1_funct_2(sK5,sK3,sK2)
% 15.04/2.49      | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 15.04/2.49      | ~ v1_funct_1(sK6)
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(sK2)
% 15.04/2.49      | v1_xboole_0(sK4)
% 15.04/2.49      | v1_xboole_0(sK3)
% 15.04/2.49      | v1_xboole_0(sK1) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_3258]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_6077,plain,
% 15.04/2.49      ( ~ m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.04/2.49      | ~ v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
% 15.04/2.49      | k2_partfun1(X0,X1,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X2) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X2) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_17]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_13191,plain,
% 15.04/2.49      ( ~ m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK4),sK2)))
% 15.04/2.49      | ~ v1_funct_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6))
% 15.04/2.49      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_6077]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18421,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),X0) ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_18340,c_37,c_36,c_35,c_34,c_33,c_32,c_30,c_29,c_28,
% 15.04/2.49                 c_27,c_26,c_25,c_4532,c_4725,c_13191]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_43264,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 15.04/2.49      | k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k1_xboole_0
% 15.04/2.49      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.49      | v1_funct_1(sK6) != iProver_top ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_43263,c_18421]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1477,plain,
% 15.04/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_6797,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_relat_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1693,c_1497]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_12,plain,
% 15.04/2.49      ( r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 15.04/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1495,plain,
% 15.04/2.49      ( k1_xboole_0 = X0 | r1_xboole_0(sK0(X0),X0) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_3720,plain,
% 15.04/2.49      ( k7_relat_1(X0,sK0(k1_relat_1(X0))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(X0) = k1_xboole_0
% 15.04/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1495,c_1500]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7218,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),sK0(k1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) = k1_xboole_0
% 15.04/2.49      | v1_funct_2(X5,X3,X1) != iProver_top
% 15.04/2.49      | v1_funct_2(X4,X2,X1) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 15.04/2.49      | v1_funct_1(X5) != iProver_top
% 15.04/2.49      | v1_funct_1(X4) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_6797,c_3720]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_21388,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k1_xboole_0
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_7218]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22268,plain,
% 15.04/2.49      ( v1_funct_1(X2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k1_xboole_0
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_21388,c_39,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22269,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k1_xboole_0
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_22268]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22284,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_22269]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22357,plain,
% 15.04/2.49      ( k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0
% 15.04/2.49      | k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)))) = k1_xboole_0
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_22284,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22358,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK0(k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_22357]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22366,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK0(k1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0 ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1477,c_22358]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_6796,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2) != iProver_top
% 15.04/2.49      | v1_partfun1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1)) = iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) != iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1693,c_1494]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1488,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2) = iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_xboole_0(X5) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1667,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2) = iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(forward_subsumption_resolution,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_1488,c_1502]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_19762,plain,
% 15.04/2.49      ( v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | v1_partfun1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1)) = iProver_top
% 15.04/2.49      | v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_6796,c_1667,c_1641]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_19763,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | v1_partfun1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1)) = iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_19762]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_19780,plain,
% 15.04/2.49      ( k1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) = k4_subset_1(X0,X2,X3)
% 15.04/2.49      | v1_funct_2(X5,X3,X1) != iProver_top
% 15.04/2.49      | v1_funct_2(X4,X2,X1) != iProver_top
% 15.04/2.49      | v4_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 15.04/2.49      | v1_funct_1(X5) != iProver_top
% 15.04/2.49      | v1_funct_1(X4) != iProver_top
% 15.04/2.49      | v1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_19763,c_1492]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1496,plain,
% 15.04/2.49      ( v4_relat_1(X0,X1) = iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_6795,plain,
% 15.04/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.04/2.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 15.04/2.49      | v4_relat_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1)) = iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 15.04/2.49      | v1_funct_1(X0) != iProver_top
% 15.04/2.49      | v1_funct_1(X3) != iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1693,c_1496]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_20228,plain,
% 15.04/2.49      ( k1_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) = k4_subset_1(X0,X2,X3)
% 15.04/2.49      | v1_funct_2(X5,X3,X1) != iProver_top
% 15.04/2.49      | v1_funct_2(X4,X2,X1) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 15.04/2.49      | v1_funct_1(X5) != iProver_top
% 15.04/2.49      | v1_funct_1(X4) != iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(X3) = iProver_top ),
% 15.04/2.49      inference(forward_subsumption_resolution,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_19780,c_6797,c_6795]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_20234,plain,
% 15.04/2.49      ( k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k4_subset_1(X0,X1,sK3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_20228]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_20947,plain,
% 15.04/2.49      ( v1_funct_1(X2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k4_subset_1(X0,X1,sK3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_20234,c_39,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_20948,plain,
% 15.04/2.49      ( k1_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5)) = k4_subset_1(X0,X1,sK3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_20947]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_20962,plain,
% 15.04/2.49      ( k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k4_subset_1(X0,sK3,sK3)
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_20948]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_21029,plain,
% 15.04/2.49      ( k1_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5)) = k4_subset_1(X0,sK3,sK3)
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_20962,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_21037,plain,
% 15.04/2.49      ( k1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) = k4_subset_1(sK1,sK3,sK3) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1477,c_21029]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22367,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK0(k4_subset_1(sK1,sK3,sK3))) = k1_xboole_0
% 15.04/2.49      | k1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) = k1_xboole_0 ),
% 15.04/2.49      inference(light_normalisation,[status(thm)],[c_22366,c_21037]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22368,plain,
% 15.04/2.49      ( k4_subset_1(sK1,sK3,sK3) = k1_xboole_0
% 15.04/2.49      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK0(k4_subset_1(sK1,sK3,sK3))) = k1_xboole_0 ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_22367,c_21037]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_17194,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK2,k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_17188]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18683,plain,
% 15.04/2.49      ( v1_funct_1(X2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | k2_partfun1(k4_subset_1(X0,X1,sK3),sK2,k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_17194,c_39,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18684,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK2,k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_18683]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18698,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,sK3,sK3),sK2,k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1)
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_18684]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18985,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,sK3,sK3),sK2,k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1)
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_18698,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18993,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK3),sK2,k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1477,c_18985]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_19,plain,
% 15.04/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.49      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 15.04/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 15.04/2.49      | ~ v1_funct_1(X0)
% 15.04/2.49      | ~ v1_funct_1(X3)
% 15.04/2.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 15.04/2.49      | v1_xboole_0(X5)
% 15.04/2.49      | v1_xboole_0(X2)
% 15.04/2.49      | v1_xboole_0(X4)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.04/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 15.04/2.49      inference(cnf_transformation,[],[f104]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_380,plain,
% 15.04/2.49      ( ~ v1_funct_1(X3)
% 15.04/2.49      | ~ v1_funct_1(X0)
% 15.04/2.49      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.49      | ~ v1_funct_2(X0,X1,X2)
% 15.04/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.49      | v1_xboole_0(X5)
% 15.04/2.49      | v1_xboole_0(X2)
% 15.04/2.49      | v1_xboole_0(X4)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.04/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_19,c_23,c_22,c_21]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_381,plain,
% 15.04/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.04/2.49      | ~ v1_funct_2(X3,X4,X2)
% 15.04/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.04/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.04/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.04/2.49      | ~ v1_funct_1(X0)
% 15.04/2.49      | ~ v1_funct_1(X3)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(X2)
% 15.04/2.49      | v1_xboole_0(X4)
% 15.04/2.49      | v1_xboole_0(X5)
% 15.04/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.04/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_380]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1472,plain,
% 15.04/2.49      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 15.04/2.49      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 15.04/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.04/2.49      | v1_funct_2(X5,X4,X1) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.04/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_funct_1(X5) != iProver_top
% 15.04/2.49      | v1_xboole_0(X3) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top
% 15.04/2.49      | v1_xboole_0(X0) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1720,plain,
% 15.04/2.49      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 15.04/2.49      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
% 15.04/2.49      | v1_funct_2(X5,X4,X1) != iProver_top
% 15.04/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 15.04/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.04/2.49      | v1_funct_1(X5) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X0) = iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(X4) = iProver_top ),
% 15.04/2.49      inference(forward_subsumption_resolution,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_1472,c_1502]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7786,plain,
% 15.04/2.49      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 15.04/2.49      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 15.04/2.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.49      | v1_funct_1(X1) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(X0) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_5063,c_1720]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_10367,plain,
% 15.04/2.49      ( v1_funct_1(X1) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 15.04/2.49      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 15.04/2.49      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 15.04/2.49      | v1_xboole_0(X0) = iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_7786,c_39,c_40,c_45,c_46,c_47]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_10368,plain,
% 15.04/2.49      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 15.04/2.49      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 15.04/2.49      | v1_funct_2(X1,X0,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 15.04/2.49      | v1_funct_1(X1) != iProver_top
% 15.04/2.49      | v1_xboole_0(X0) = iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_10367]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_10382,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,sK3,sK3),sK2,k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK3) = sK5
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_5063,c_10368]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_10693,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,sK3,sK3),sK2,k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),sK3) = sK5
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_10382,c_40,c_45,c_46,c_47]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_10701,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK3),sK2,k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK3) = sK5 ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1477,c_10693]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_19001,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),sK3) = sK5 ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_18993,c_10701]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2,plain,
% 15.04/2.49      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.04/2.49      inference(cnf_transformation,[],[f98]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_7219,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_setfam_1(k2_tarski(X6,X7))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),X6),X7)
% 15.04/2.49      | v1_funct_2(X5,X3,X1) != iProver_top
% 15.04/2.49      | v1_funct_2(X4,X2,X1) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 15.04/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 15.04/2.49      | v1_funct_1(X5) != iProver_top
% 15.04/2.49      | v1_funct_1(X4) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(X2) = iProver_top
% 15.04/2.49      | v1_xboole_0(X3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_6797,c_1501]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_13226,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),k1_setfam_1(k2_tarski(X3,X4))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3),X4)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_7219]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_13609,plain,
% 15.04/2.49      ( v1_funct_1(X2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),k1_setfam_1(k2_tarski(X3,X4))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3),X4)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_13226,c_39,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_13610,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),k1_setfam_1(k2_tarski(X3,X4))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,X1,sK3,X2,sK5),X3),X4)
% 15.04/2.49      | v1_funct_2(X2,X1,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(X2) != iProver_top
% 15.04/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_13609]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_13624,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1),X2)
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1483,c_13610]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_13691,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(k1_tmap_1(X0,sK2,sK3,sK3,sK5,sK5),X1),X2)
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_13624,c_40,c_45,c_46]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_13699,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0),X1) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_1477,c_13691]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_13877,plain,
% 15.04/2.49      ( k7_relat_1(k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0),k1_xboole_0) = k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_xboole_0) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_2,c_13699]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_22854,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_19001,c_13877]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_23216,plain,
% 15.04/2.49      ( k7_relat_1(k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0),k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_22854,c_13877]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_27495,plain,
% 15.04/2.49      ( k4_subset_1(sK1,sK3,sK3) = k1_xboole_0
% 15.04/2.49      | k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_22368,c_23216]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_27498,plain,
% 15.04/2.49      ( k4_subset_1(sK1,sK3,sK3) = k1_xboole_0
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_27495,c_6]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_21289,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0
% 15.04/2.49      | r1_xboole_0(X0,k4_subset_1(sK1,sK3,sK3)) != iProver_top
% 15.04/2.49      | v1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) != iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_21037,c_1500]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_38,plain,
% 15.04/2.49      ( v1_xboole_0(sK1) != iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2429,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK5,X0,X1)
% 15.04/2.49      | ~ v1_funct_2(sK5,X2,X1)
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 15.04/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 15.04/2.49      | m1_subset_1(k1_tmap_1(X3,X1,X2,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X0),X1)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(X2)
% 15.04/2.49      | v1_xboole_0(X3) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2086]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_2972,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK5,X0,sK2)
% 15.04/2.49      | ~ v1_funct_2(sK5,sK3,sK2)
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.04/2.49      | m1_subset_1(k1_tmap_1(X1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,sK3,X0),sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(X1)
% 15.04/2.49      | v1_xboole_0(sK2)
% 15.04/2.49      | v1_xboole_0(sK3) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2429]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_3263,plain,
% 15.04/2.49      ( ~ v1_funct_2(sK5,X0,sK2)
% 15.04/2.49      | ~ v1_funct_2(sK5,sK3,sK2)
% 15.04/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
% 15.04/2.49      | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X0),sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 15.04/2.49      | ~ v1_funct_1(sK5)
% 15.04/2.49      | v1_xboole_0(X0)
% 15.04/2.49      | v1_xboole_0(sK2)
% 15.04/2.49      | v1_xboole_0(sK3)
% 15.04/2.49      | v1_xboole_0(sK1) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_2972]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_3264,plain,
% 15.04/2.49      ( v1_funct_2(sK5,X0,sK2) != iProver_top
% 15.04/2.49      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.49      | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X0),sK2))) = iProver_top
% 15.04/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(X0) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK1) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_3263]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_3266,plain,
% 15.04/2.49      ( v1_funct_2(sK5,sK3,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK3),sK2))) = iProver_top
% 15.04/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK5) != iProver_top
% 15.04/2.49      | v1_xboole_0(sK2) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK3) = iProver_top
% 15.04/2.49      | v1_xboole_0(sK1) = iProver_top ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_3264]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_4745,plain,
% 15.04/2.49      ( ~ m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X0),sK2)))
% 15.04/2.49      | v1_relat_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5)) ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_4746,plain,
% 15.04/2.49      ( m1_subset_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,X0),sK2))) != iProver_top
% 15.04/2.49      | v1_relat_1(k1_tmap_1(sK1,sK2,sK3,X0,sK5,sK5)) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_4745]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_4748,plain,
% 15.04/2.49      ( m1_subset_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK1,sK3,sK3),sK2))) != iProver_top
% 15.04/2.49      | v1_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5)) = iProver_top ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_4746]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_24575,plain,
% 15.04/2.49      ( r1_xboole_0(X0,k4_subset_1(sK1,sK3,sK3)) != iProver_top
% 15.04/2.49      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0 ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_21289,c_38,c_39,c_40,c_41,c_45,c_46,c_47,c_3266,
% 15.04/2.49                 c_4748]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_24576,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0
% 15.04/2.49      | r1_xboole_0(X0,k4_subset_1(sK1,sK3,sK3)) != iProver_top ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_24575]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_27540,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0
% 15.04/2.49      | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_27498,c_24576]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_0,plain,
% 15.04/2.49      ( r1_xboole_0(X0,X1)
% 15.04/2.49      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 15.04/2.49      inference(cnf_transformation,[],[f96]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1901,plain,
% 15.04/2.49      ( r1_xboole_0(X0,k1_xboole_0)
% 15.04/2.49      | k1_setfam_1(k2_tarski(X0,k1_xboole_0)) != k1_xboole_0 ),
% 15.04/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_1902,plain,
% 15.04/2.49      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) != k1_xboole_0
% 15.04/2.49      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 15.04/2.49      inference(predicate_to_equality,[status(thm)],[c_1901]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_27778,plain,
% 15.04/2.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0
% 15.04/2.49      | k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0 ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_27540,c_2,c_1902]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_27779,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK3,sK5,sK5),X0) = k1_xboole_0
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 15.04/2.49      inference(renaming,[status(thm)],[c_27778]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_27797,plain,
% 15.04/2.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_27779,c_22854]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_5125,plain,
% 15.04/2.49      ( k7_relat_1(k7_relat_1(sK5,sK3),sK4) = k7_relat_1(sK5,k1_xboole_0) ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_4004,c_3075]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_29905,plain,
% 15.04/2.49      ( k7_relat_1(k7_relat_1(sK5,sK3),sK4) = k1_xboole_0 ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_27797,c_5125]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_24,negated_conjecture,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 15.04/2.49      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 15.04/2.49      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 15.04/2.49      inference(cnf_transformation,[],[f95]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_3185,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 15.04/2.49      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 15.04/2.49      | k2_partfun1(sK4,sK2,sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k2_partfun1(sK3,sK2,sK5,k1_setfam_1(k2_tarski(sK3,sK4))) ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_2987,c_24]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_4212,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 15.04/2.49      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 15.04/2.49      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_4004,c_3185]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_5061,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 15.04/2.49      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 15.04/2.49      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_5057,c_4212]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_5238,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 15.04/2.49      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_5061,c_5063]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_8116,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 15.04/2.49      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_7344,c_5238]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_10381,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 15.04/2.49      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 15.04/2.49      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 15.04/2.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | v1_funct_1(sK6) != iProver_top
% 15.04/2.49      | v1_xboole_0(sK4) = iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_5057,c_10368]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_11019,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 15.04/2.49      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_10381,c_42,c_48,c_49,c_50]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_11029,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 15.04/2.49      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 15.04/2.49      inference(superposition,[status(thm)],[c_2987,c_11019]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_11030,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 15.04/2.49      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 15.04/2.49      inference(light_normalisation,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_11029,c_4004,c_7344]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_11031,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 15.04/2.49      | k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k1_xboole_0
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_11030,c_2987,c_3075]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_11032,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 15.04/2.49      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 15.04/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 15.04/2.49      inference(light_normalisation,[status(thm)],[c_11031,c_5125]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_11033,plain,
% 15.04/2.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 15.04/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 15.04/2.49      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 15.04/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_11032]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_11730,plain,
% 15.04/2.49      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 15.04/2.49      inference(global_propositional_subsumption,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_8116,c_34,c_32,c_11033]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(c_18425,plain,
% 15.04/2.49      ( k7_relat_1(k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 15.04/2.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 15.04/2.49      inference(demodulation,[status(thm)],[c_18421,c_11730]) ).
% 15.04/2.49  
% 15.04/2.49  cnf(contradiction,plain,
% 15.04/2.49      ( $false ),
% 15.04/2.49      inference(minisat,
% 15.04/2.49                [status(thm)],
% 15.04/2.49                [c_43264,c_29905,c_27797,c_18425,c_50,c_49,c_48]) ).
% 15.04/2.49  
% 15.04/2.49  
% 15.04/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.04/2.49  
% 15.04/2.49  ------                               Statistics
% 15.04/2.49  
% 15.04/2.49  ------ Selected
% 15.04/2.49  
% 15.04/2.49  total_time:                             1.66
% 15.04/2.49  
%------------------------------------------------------------------------------
