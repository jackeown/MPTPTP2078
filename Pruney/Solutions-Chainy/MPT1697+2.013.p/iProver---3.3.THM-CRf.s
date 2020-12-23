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
% DateTime   : Thu Dec  3 12:21:24 EST 2020

% Result     : Theorem 6.99s
% Output     : CNFRefutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :  281 (7302 expanded)
%              Number of clauses        :  168 (1855 expanded)
%              Number of leaves         :   31 (2587 expanded)
%              Depth                    :   33
%              Number of atoms          : 1291 (77748 expanded)
%              Number of equality atoms :  510 (17960 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
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

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f75,plain,(
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

fof(f74,plain,(
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

fof(f73,plain,(
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

fof(f72,plain,(
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

fof(f71,plain,(
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

fof(f70,plain,
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

fof(f76,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f60,f75,f74,f73,f72,f71,f70])).

fof(f117,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f76])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f80,f82])).

fof(f124,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f76])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f122,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f76])).

fof(f121,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f76])).

fof(f119,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

fof(f23,axiom,(
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

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f106,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f133,plain,(
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
    inference(equality_resolution,[],[f106])).

fof(f24,axiom,(
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

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f110,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f111,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f114,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f120,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f116,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f76])).

fof(f123,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f118,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f76])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f82])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f49])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f95,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r1_xboole_0(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
     => r1_xboole_0(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f65])).

fof(f100,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f107,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f132,plain,(
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
    inference(equality_resolution,[],[f107])).

fof(f125,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f76])).

fof(f115,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2534,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_2559,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4795,plain,
    ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_2534,c_2559])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2540,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2545,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6834,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_2545])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3046,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3406,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_7054,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6834,c_37,c_35,c_3406])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2537,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6835,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_2545])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3051,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3411,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_3051])).

cnf(c_7262,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6835,c_40,c_38,c_3411])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f133])).

cnf(c_33,plain,
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
    inference(cnf_transformation,[],[f109])).

cnf(c_32,plain,
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
    inference(cnf_transformation,[],[f110])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f111])).

cnf(c_258,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_33,c_32,c_31])).

cnf(c_259,plain,
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
    inference(renaming,[status(thm)],[c_258])).

cnf(c_2528,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2558,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2823,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2528,c_2558])).

cnf(c_10535,plain,
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
    inference(superposition,[status(thm)],[c_7262,c_2823])).

cnf(c_46,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_49,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_50,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_55,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_56,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_57,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_12830,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10535,c_49,c_50,c_55,c_56,c_57])).

cnf(c_12831,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_12830])).

cnf(c_12842,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7054,c_12831])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_52,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_58,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_59,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_60,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_14801,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12842,c_52,c_58,c_59,c_60])).

cnf(c_14811,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4795,c_14801])).

cnf(c_19,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_41,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_638,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_41])).

cnf(c_639,plain,
    ( r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_641,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_639,c_45,c_43])).

cnf(c_2526,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2561,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3672,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2526,c_2561])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2547,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3887,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_2547])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_26,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_651,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_21,c_26])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_26,c_21,c_20])).

cnf(c_654,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_653])).

cnf(c_711,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_23,c_654])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_711,c_26,c_23,c_21,c_20])).

cnf(c_714,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_713])).

cnf(c_2524,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_3422,plain,
    ( k1_relat_1(sK6) = sK4
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_2524])).

cnf(c_3563,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3422,c_49,c_58,c_59])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2552,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5284,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3563,c_2552])).

cnf(c_2968,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2969,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2968])).

cnf(c_7267,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5284,c_60,c_2969])).

cnf(c_7268,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7267])).

cnf(c_7276,plain,
    ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2526,c_7268])).

cnf(c_16,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2549,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7484,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7276,c_2549])).

cnf(c_13,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_7492,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7484,c_13])).

cnf(c_8127,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7492,c_60,c_2969])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2556,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8132,plain,
    ( k7_relat_1(k7_relat_1(X0,sK3),k1_xboole_0) = k7_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8127,c_2556])).

cnf(c_10154,plain,
    ( k7_relat_1(k7_relat_1(sK6,sK3),k1_xboole_0) = k7_relat_1(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3887,c_8132])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2557,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7485,plain,
    ( v1_relat_1(sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7276,c_2557])).

cnf(c_8320,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7485,c_60,c_2969])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2548,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8326,plain,
    ( k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8320,c_2548])).

cnf(c_8328,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8326,c_13])).

cnf(c_10159,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10154,c_7276,c_8328])).

cnf(c_14812,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14811,c_3672,c_10159])).

cnf(c_14813,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14812,c_4795])).

cnf(c_22,plain,
    ( r1_xboole_0(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2546,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3418,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_2524])).

cnf(c_3502,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_49,c_55,c_56])).

cnf(c_5285,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3502,c_2552])).

cnf(c_2971,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2972,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2971])).

cnf(c_7498,plain,
    ( r1_xboole_0(X0,sK3) != iProver_top
    | k7_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5285,c_57,c_2972])).

cnf(c_7499,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7498])).

cnf(c_7506,plain,
    ( k7_relat_1(sK5,sK0(sK3)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2546,c_7499])).

cnf(c_3888,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_2547])).

cnf(c_9146,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(k1_xboole_0),sK0(sK3)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7506,c_2549])).

cnf(c_9151,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK0(sK3)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9146,c_13])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_142,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_144,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_1587,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4216,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_4217,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4216])).

cnf(c_4219,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4217])).

cnf(c_9354,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8328,c_2549])).

cnf(c_9358,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9354,c_13])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2555,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8325,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8320,c_2555])).

cnf(c_12,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_8331,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8325,c_12,c_13])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2553,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9397,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8331,c_2553])).

cnf(c_9398,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9397,c_13])).

cnf(c_10102,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9151,c_50,c_57,c_60,c_144,c_2969,c_2972,c_4219,c_7485,c_9358,c_9398])).

cnf(c_10107,plain,
    ( k7_relat_1(k7_relat_1(X0,sK0(sK3)),k1_xboole_0) = k7_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10102,c_2556])).

cnf(c_11518,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK0(sK3)),k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3888,c_10107])).

cnf(c_11601,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7506,c_11518])).

cnf(c_11610,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11601,c_8328])).

cnf(c_12115,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11610,c_50,c_60,c_144,c_2969,c_4219,c_7485,c_9358,c_9398])).

cnf(c_14814,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14813,c_3672,c_12115])).

cnf(c_14815,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14814])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_265,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_33,c_32,c_31])).

cnf(c_266,plain,
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
    inference(renaming,[status(thm)],[c_265])).

cnf(c_2527,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_2795,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2527,c_2558])).

cnf(c_9750,plain,
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
    inference(superposition,[status(thm)],[c_7262,c_2795])).

cnf(c_11005,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9750,c_49,c_50,c_55,c_56,c_57])).

cnf(c_11006,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11005])).

cnf(c_11017,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7054,c_11006])).

cnf(c_11216,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11017,c_52,c_58,c_59,c_60])).

cnf(c_11226,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4795,c_11216])).

cnf(c_11227,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11226,c_3672,c_10159])).

cnf(c_11228,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11227,c_4795])).

cnf(c_11229,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11228,c_3672])).

cnf(c_11230,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11229])).

cnf(c_34,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_4810,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK4,sK2,sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k2_partfun1(sK3,sK2,sK5,k1_setfam_1(k2_tarski(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_4795,c_34])).

cnf(c_4811,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4810,c_3672])).

cnf(c_7058,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7054,c_4811])).

cnf(c_8461,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7058,c_7262])).

cnf(c_10824,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10159,c_8461])).

cnf(c_53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14815,c_11610,c_11230,c_10824,c_9398,c_9358,c_7485,c_4219,c_2969,c_144,c_60,c_53,c_42,c_51,c_44,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:14:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 6.99/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.99/1.52  
% 6.99/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.99/1.52  
% 6.99/1.52  ------  iProver source info
% 6.99/1.52  
% 6.99/1.52  git: date: 2020-06-30 10:37:57 +0100
% 6.99/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.99/1.52  git: non_committed_changes: false
% 6.99/1.52  git: last_make_outside_of_git: false
% 6.99/1.52  
% 6.99/1.52  ------ 
% 6.99/1.52  
% 6.99/1.52  ------ Input Options
% 6.99/1.52  
% 6.99/1.52  --out_options                           all
% 6.99/1.52  --tptp_safe_out                         true
% 6.99/1.52  --problem_path                          ""
% 6.99/1.52  --include_path                          ""
% 6.99/1.52  --clausifier                            res/vclausify_rel
% 6.99/1.52  --clausifier_options                    --mode clausify
% 6.99/1.52  --stdin                                 false
% 6.99/1.52  --stats_out                             all
% 6.99/1.52  
% 6.99/1.52  ------ General Options
% 6.99/1.52  
% 6.99/1.52  --fof                                   false
% 6.99/1.52  --time_out_real                         305.
% 6.99/1.52  --time_out_virtual                      -1.
% 6.99/1.52  --symbol_type_check                     false
% 6.99/1.52  --clausify_out                          false
% 6.99/1.52  --sig_cnt_out                           false
% 6.99/1.52  --trig_cnt_out                          false
% 6.99/1.52  --trig_cnt_out_tolerance                1.
% 6.99/1.52  --trig_cnt_out_sk_spl                   false
% 6.99/1.52  --abstr_cl_out                          false
% 6.99/1.52  
% 6.99/1.52  ------ Global Options
% 6.99/1.52  
% 6.99/1.52  --schedule                              default
% 6.99/1.52  --add_important_lit                     false
% 6.99/1.52  --prop_solver_per_cl                    1000
% 6.99/1.52  --min_unsat_core                        false
% 6.99/1.52  --soft_assumptions                      false
% 6.99/1.52  --soft_lemma_size                       3
% 6.99/1.52  --prop_impl_unit_size                   0
% 6.99/1.52  --prop_impl_unit                        []
% 6.99/1.52  --share_sel_clauses                     true
% 6.99/1.52  --reset_solvers                         false
% 6.99/1.52  --bc_imp_inh                            [conj_cone]
% 6.99/1.52  --conj_cone_tolerance                   3.
% 6.99/1.52  --extra_neg_conj                        none
% 6.99/1.52  --large_theory_mode                     true
% 6.99/1.52  --prolific_symb_bound                   200
% 6.99/1.52  --lt_threshold                          2000
% 6.99/1.52  --clause_weak_htbl                      true
% 6.99/1.52  --gc_record_bc_elim                     false
% 6.99/1.52  
% 6.99/1.52  ------ Preprocessing Options
% 6.99/1.52  
% 6.99/1.52  --preprocessing_flag                    true
% 6.99/1.52  --time_out_prep_mult                    0.1
% 6.99/1.52  --splitting_mode                        input
% 6.99/1.52  --splitting_grd                         true
% 6.99/1.52  --splitting_cvd                         false
% 6.99/1.52  --splitting_cvd_svl                     false
% 6.99/1.52  --splitting_nvd                         32
% 6.99/1.52  --sub_typing                            true
% 6.99/1.52  --prep_gs_sim                           true
% 6.99/1.52  --prep_unflatten                        true
% 6.99/1.52  --prep_res_sim                          true
% 6.99/1.52  --prep_upred                            true
% 6.99/1.52  --prep_sem_filter                       exhaustive
% 6.99/1.52  --prep_sem_filter_out                   false
% 6.99/1.52  --pred_elim                             true
% 6.99/1.52  --res_sim_input                         true
% 6.99/1.52  --eq_ax_congr_red                       true
% 6.99/1.52  --pure_diseq_elim                       true
% 6.99/1.52  --brand_transform                       false
% 6.99/1.52  --non_eq_to_eq                          false
% 6.99/1.52  --prep_def_merge                        true
% 6.99/1.52  --prep_def_merge_prop_impl              false
% 6.99/1.52  --prep_def_merge_mbd                    true
% 6.99/1.52  --prep_def_merge_tr_red                 false
% 6.99/1.52  --prep_def_merge_tr_cl                  false
% 6.99/1.52  --smt_preprocessing                     true
% 6.99/1.52  --smt_ac_axioms                         fast
% 6.99/1.52  --preprocessed_out                      false
% 6.99/1.52  --preprocessed_stats                    false
% 6.99/1.52  
% 6.99/1.52  ------ Abstraction refinement Options
% 6.99/1.52  
% 6.99/1.52  --abstr_ref                             []
% 6.99/1.52  --abstr_ref_prep                        false
% 6.99/1.52  --abstr_ref_until_sat                   false
% 6.99/1.52  --abstr_ref_sig_restrict                funpre
% 6.99/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 6.99/1.52  --abstr_ref_under                       []
% 6.99/1.52  
% 6.99/1.52  ------ SAT Options
% 6.99/1.52  
% 6.99/1.52  --sat_mode                              false
% 6.99/1.52  --sat_fm_restart_options                ""
% 6.99/1.52  --sat_gr_def                            false
% 6.99/1.52  --sat_epr_types                         true
% 6.99/1.52  --sat_non_cyclic_types                  false
% 6.99/1.52  --sat_finite_models                     false
% 6.99/1.52  --sat_fm_lemmas                         false
% 6.99/1.52  --sat_fm_prep                           false
% 6.99/1.52  --sat_fm_uc_incr                        true
% 6.99/1.52  --sat_out_model                         small
% 6.99/1.52  --sat_out_clauses                       false
% 6.99/1.52  
% 6.99/1.52  ------ QBF Options
% 6.99/1.52  
% 6.99/1.52  --qbf_mode                              false
% 6.99/1.52  --qbf_elim_univ                         false
% 6.99/1.52  --qbf_dom_inst                          none
% 6.99/1.52  --qbf_dom_pre_inst                      false
% 6.99/1.52  --qbf_sk_in                             false
% 6.99/1.52  --qbf_pred_elim                         true
% 6.99/1.52  --qbf_split                             512
% 6.99/1.52  
% 6.99/1.52  ------ BMC1 Options
% 6.99/1.52  
% 6.99/1.52  --bmc1_incremental                      false
% 6.99/1.52  --bmc1_axioms                           reachable_all
% 6.99/1.52  --bmc1_min_bound                        0
% 6.99/1.52  --bmc1_max_bound                        -1
% 6.99/1.52  --bmc1_max_bound_default                -1
% 6.99/1.52  --bmc1_symbol_reachability              true
% 6.99/1.52  --bmc1_property_lemmas                  false
% 6.99/1.52  --bmc1_k_induction                      false
% 6.99/1.52  --bmc1_non_equiv_states                 false
% 6.99/1.52  --bmc1_deadlock                         false
% 6.99/1.52  --bmc1_ucm                              false
% 6.99/1.52  --bmc1_add_unsat_core                   none
% 6.99/1.52  --bmc1_unsat_core_children              false
% 6.99/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.99/1.52  --bmc1_out_stat                         full
% 6.99/1.52  --bmc1_ground_init                      false
% 6.99/1.52  --bmc1_pre_inst_next_state              false
% 6.99/1.52  --bmc1_pre_inst_state                   false
% 6.99/1.52  --bmc1_pre_inst_reach_state             false
% 6.99/1.52  --bmc1_out_unsat_core                   false
% 6.99/1.52  --bmc1_aig_witness_out                  false
% 6.99/1.52  --bmc1_verbose                          false
% 6.99/1.52  --bmc1_dump_clauses_tptp                false
% 6.99/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.99/1.52  --bmc1_dump_file                        -
% 6.99/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.99/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.99/1.52  --bmc1_ucm_extend_mode                  1
% 6.99/1.52  --bmc1_ucm_init_mode                    2
% 6.99/1.52  --bmc1_ucm_cone_mode                    none
% 6.99/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.99/1.52  --bmc1_ucm_relax_model                  4
% 6.99/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.99/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.99/1.52  --bmc1_ucm_layered_model                none
% 6.99/1.52  --bmc1_ucm_max_lemma_size               10
% 6.99/1.52  
% 6.99/1.52  ------ AIG Options
% 6.99/1.52  
% 6.99/1.52  --aig_mode                              false
% 6.99/1.52  
% 6.99/1.52  ------ Instantiation Options
% 6.99/1.52  
% 6.99/1.52  --instantiation_flag                    true
% 6.99/1.52  --inst_sos_flag                         false
% 6.99/1.52  --inst_sos_phase                        true
% 6.99/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.99/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.99/1.52  --inst_lit_sel_side                     num_symb
% 6.99/1.52  --inst_solver_per_active                1400
% 6.99/1.52  --inst_solver_calls_frac                1.
% 6.99/1.52  --inst_passive_queue_type               priority_queues
% 6.99/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.99/1.52  --inst_passive_queues_freq              [25;2]
% 6.99/1.52  --inst_dismatching                      true
% 6.99/1.52  --inst_eager_unprocessed_to_passive     true
% 6.99/1.52  --inst_prop_sim_given                   true
% 6.99/1.52  --inst_prop_sim_new                     false
% 6.99/1.52  --inst_subs_new                         false
% 6.99/1.52  --inst_eq_res_simp                      false
% 6.99/1.52  --inst_subs_given                       false
% 6.99/1.52  --inst_orphan_elimination               true
% 6.99/1.52  --inst_learning_loop_flag               true
% 6.99/1.52  --inst_learning_start                   3000
% 6.99/1.52  --inst_learning_factor                  2
% 6.99/1.52  --inst_start_prop_sim_after_learn       3
% 6.99/1.52  --inst_sel_renew                        solver
% 6.99/1.52  --inst_lit_activity_flag                true
% 6.99/1.52  --inst_restr_to_given                   false
% 6.99/1.52  --inst_activity_threshold               500
% 6.99/1.52  --inst_out_proof                        true
% 6.99/1.52  
% 6.99/1.52  ------ Resolution Options
% 6.99/1.52  
% 6.99/1.52  --resolution_flag                       true
% 6.99/1.52  --res_lit_sel                           adaptive
% 6.99/1.52  --res_lit_sel_side                      none
% 6.99/1.52  --res_ordering                          kbo
% 6.99/1.52  --res_to_prop_solver                    active
% 6.99/1.52  --res_prop_simpl_new                    false
% 6.99/1.52  --res_prop_simpl_given                  true
% 6.99/1.52  --res_passive_queue_type                priority_queues
% 6.99/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.99/1.52  --res_passive_queues_freq               [15;5]
% 6.99/1.52  --res_forward_subs                      full
% 6.99/1.52  --res_backward_subs                     full
% 6.99/1.52  --res_forward_subs_resolution           true
% 6.99/1.52  --res_backward_subs_resolution          true
% 6.99/1.52  --res_orphan_elimination                true
% 6.99/1.52  --res_time_limit                        2.
% 6.99/1.52  --res_out_proof                         true
% 6.99/1.52  
% 6.99/1.52  ------ Superposition Options
% 6.99/1.52  
% 6.99/1.52  --superposition_flag                    true
% 6.99/1.52  --sup_passive_queue_type                priority_queues
% 6.99/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.99/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.99/1.52  --demod_completeness_check              fast
% 6.99/1.52  --demod_use_ground                      true
% 6.99/1.52  --sup_to_prop_solver                    passive
% 6.99/1.52  --sup_prop_simpl_new                    true
% 6.99/1.52  --sup_prop_simpl_given                  true
% 6.99/1.52  --sup_fun_splitting                     false
% 6.99/1.52  --sup_smt_interval                      50000
% 6.99/1.52  
% 6.99/1.52  ------ Superposition Simplification Setup
% 6.99/1.52  
% 6.99/1.52  --sup_indices_passive                   []
% 6.99/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.99/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.52  --sup_full_bw                           [BwDemod]
% 6.99/1.52  --sup_immed_triv                        [TrivRules]
% 6.99/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.99/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.52  --sup_immed_bw_main                     []
% 6.99/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.99/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.52  
% 6.99/1.52  ------ Combination Options
% 6.99/1.52  
% 6.99/1.52  --comb_res_mult                         3
% 6.99/1.52  --comb_sup_mult                         2
% 6.99/1.52  --comb_inst_mult                        10
% 6.99/1.52  
% 6.99/1.52  ------ Debug Options
% 6.99/1.52  
% 6.99/1.52  --dbg_backtrace                         false
% 6.99/1.52  --dbg_dump_prop_clauses                 false
% 6.99/1.52  --dbg_dump_prop_clauses_file            -
% 6.99/1.52  --dbg_out_stat                          false
% 6.99/1.52  ------ Parsing...
% 6.99/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.99/1.52  
% 6.99/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 6.99/1.52  
% 6.99/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.99/1.52  
% 6.99/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.99/1.52  ------ Proving...
% 6.99/1.52  ------ Problem Properties 
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  clauses                                 42
% 6.99/1.52  conjectures                             13
% 6.99/1.52  EPR                                     10
% 6.99/1.52  Horn                                    34
% 6.99/1.52  unary                                   15
% 6.99/1.52  binary                                  10
% 6.99/1.52  lits                                    154
% 6.99/1.52  lits eq                                 28
% 6.99/1.52  fd_pure                                 0
% 6.99/1.52  fd_pseudo                               0
% 6.99/1.52  fd_cond                                 1
% 6.99/1.52  fd_pseudo_cond                          1
% 6.99/1.52  AC symbols                              0
% 6.99/1.52  
% 6.99/1.52  ------ Schedule dynamic 5 is on 
% 6.99/1.52  
% 6.99/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  ------ 
% 6.99/1.52  Current options:
% 6.99/1.52  ------ 
% 6.99/1.52  
% 6.99/1.52  ------ Input Options
% 6.99/1.52  
% 6.99/1.52  --out_options                           all
% 6.99/1.52  --tptp_safe_out                         true
% 6.99/1.52  --problem_path                          ""
% 6.99/1.52  --include_path                          ""
% 6.99/1.52  --clausifier                            res/vclausify_rel
% 6.99/1.52  --clausifier_options                    --mode clausify
% 6.99/1.52  --stdin                                 false
% 6.99/1.52  --stats_out                             all
% 6.99/1.52  
% 6.99/1.52  ------ General Options
% 6.99/1.52  
% 6.99/1.52  --fof                                   false
% 6.99/1.52  --time_out_real                         305.
% 6.99/1.52  --time_out_virtual                      -1.
% 6.99/1.52  --symbol_type_check                     false
% 6.99/1.52  --clausify_out                          false
% 6.99/1.52  --sig_cnt_out                           false
% 6.99/1.52  --trig_cnt_out                          false
% 6.99/1.52  --trig_cnt_out_tolerance                1.
% 6.99/1.52  --trig_cnt_out_sk_spl                   false
% 6.99/1.52  --abstr_cl_out                          false
% 6.99/1.52  
% 6.99/1.52  ------ Global Options
% 6.99/1.52  
% 6.99/1.52  --schedule                              default
% 6.99/1.52  --add_important_lit                     false
% 6.99/1.52  --prop_solver_per_cl                    1000
% 6.99/1.52  --min_unsat_core                        false
% 6.99/1.52  --soft_assumptions                      false
% 6.99/1.52  --soft_lemma_size                       3
% 6.99/1.52  --prop_impl_unit_size                   0
% 6.99/1.52  --prop_impl_unit                        []
% 6.99/1.52  --share_sel_clauses                     true
% 6.99/1.52  --reset_solvers                         false
% 6.99/1.52  --bc_imp_inh                            [conj_cone]
% 6.99/1.52  --conj_cone_tolerance                   3.
% 6.99/1.52  --extra_neg_conj                        none
% 6.99/1.52  --large_theory_mode                     true
% 6.99/1.52  --prolific_symb_bound                   200
% 6.99/1.52  --lt_threshold                          2000
% 6.99/1.52  --clause_weak_htbl                      true
% 6.99/1.52  --gc_record_bc_elim                     false
% 6.99/1.52  
% 6.99/1.52  ------ Preprocessing Options
% 6.99/1.52  
% 6.99/1.52  --preprocessing_flag                    true
% 6.99/1.52  --time_out_prep_mult                    0.1
% 6.99/1.52  --splitting_mode                        input
% 6.99/1.52  --splitting_grd                         true
% 6.99/1.52  --splitting_cvd                         false
% 6.99/1.52  --splitting_cvd_svl                     false
% 6.99/1.52  --splitting_nvd                         32
% 6.99/1.52  --sub_typing                            true
% 6.99/1.52  --prep_gs_sim                           true
% 6.99/1.52  --prep_unflatten                        true
% 6.99/1.52  --prep_res_sim                          true
% 6.99/1.52  --prep_upred                            true
% 6.99/1.52  --prep_sem_filter                       exhaustive
% 6.99/1.52  --prep_sem_filter_out                   false
% 6.99/1.52  --pred_elim                             true
% 6.99/1.52  --res_sim_input                         true
% 6.99/1.52  --eq_ax_congr_red                       true
% 6.99/1.52  --pure_diseq_elim                       true
% 6.99/1.52  --brand_transform                       false
% 6.99/1.52  --non_eq_to_eq                          false
% 6.99/1.52  --prep_def_merge                        true
% 6.99/1.52  --prep_def_merge_prop_impl              false
% 6.99/1.52  --prep_def_merge_mbd                    true
% 6.99/1.52  --prep_def_merge_tr_red                 false
% 6.99/1.52  --prep_def_merge_tr_cl                  false
% 6.99/1.52  --smt_preprocessing                     true
% 6.99/1.52  --smt_ac_axioms                         fast
% 6.99/1.52  --preprocessed_out                      false
% 6.99/1.52  --preprocessed_stats                    false
% 6.99/1.52  
% 6.99/1.52  ------ Abstraction refinement Options
% 6.99/1.52  
% 6.99/1.52  --abstr_ref                             []
% 6.99/1.52  --abstr_ref_prep                        false
% 6.99/1.52  --abstr_ref_until_sat                   false
% 6.99/1.52  --abstr_ref_sig_restrict                funpre
% 6.99/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 6.99/1.52  --abstr_ref_under                       []
% 6.99/1.52  
% 6.99/1.52  ------ SAT Options
% 6.99/1.52  
% 6.99/1.52  --sat_mode                              false
% 6.99/1.52  --sat_fm_restart_options                ""
% 6.99/1.52  --sat_gr_def                            false
% 6.99/1.52  --sat_epr_types                         true
% 6.99/1.52  --sat_non_cyclic_types                  false
% 6.99/1.52  --sat_finite_models                     false
% 6.99/1.52  --sat_fm_lemmas                         false
% 6.99/1.52  --sat_fm_prep                           false
% 6.99/1.52  --sat_fm_uc_incr                        true
% 6.99/1.52  --sat_out_model                         small
% 6.99/1.52  --sat_out_clauses                       false
% 6.99/1.52  
% 6.99/1.52  ------ QBF Options
% 6.99/1.52  
% 6.99/1.52  --qbf_mode                              false
% 6.99/1.52  --qbf_elim_univ                         false
% 6.99/1.52  --qbf_dom_inst                          none
% 6.99/1.52  --qbf_dom_pre_inst                      false
% 6.99/1.52  --qbf_sk_in                             false
% 6.99/1.52  --qbf_pred_elim                         true
% 6.99/1.52  --qbf_split                             512
% 6.99/1.52  
% 6.99/1.52  ------ BMC1 Options
% 6.99/1.52  
% 6.99/1.52  --bmc1_incremental                      false
% 6.99/1.52  --bmc1_axioms                           reachable_all
% 6.99/1.52  --bmc1_min_bound                        0
% 6.99/1.52  --bmc1_max_bound                        -1
% 6.99/1.52  --bmc1_max_bound_default                -1
% 6.99/1.52  --bmc1_symbol_reachability              true
% 6.99/1.52  --bmc1_property_lemmas                  false
% 6.99/1.52  --bmc1_k_induction                      false
% 6.99/1.52  --bmc1_non_equiv_states                 false
% 6.99/1.52  --bmc1_deadlock                         false
% 6.99/1.52  --bmc1_ucm                              false
% 6.99/1.52  --bmc1_add_unsat_core                   none
% 6.99/1.52  --bmc1_unsat_core_children              false
% 6.99/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.99/1.52  --bmc1_out_stat                         full
% 6.99/1.52  --bmc1_ground_init                      false
% 6.99/1.52  --bmc1_pre_inst_next_state              false
% 6.99/1.52  --bmc1_pre_inst_state                   false
% 6.99/1.52  --bmc1_pre_inst_reach_state             false
% 6.99/1.52  --bmc1_out_unsat_core                   false
% 6.99/1.52  --bmc1_aig_witness_out                  false
% 6.99/1.52  --bmc1_verbose                          false
% 6.99/1.52  --bmc1_dump_clauses_tptp                false
% 6.99/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.99/1.52  --bmc1_dump_file                        -
% 6.99/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.99/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.99/1.52  --bmc1_ucm_extend_mode                  1
% 6.99/1.52  --bmc1_ucm_init_mode                    2
% 6.99/1.52  --bmc1_ucm_cone_mode                    none
% 6.99/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.99/1.52  --bmc1_ucm_relax_model                  4
% 6.99/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.99/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.99/1.52  --bmc1_ucm_layered_model                none
% 6.99/1.52  --bmc1_ucm_max_lemma_size               10
% 6.99/1.52  
% 6.99/1.52  ------ AIG Options
% 6.99/1.52  
% 6.99/1.52  --aig_mode                              false
% 6.99/1.52  
% 6.99/1.52  ------ Instantiation Options
% 6.99/1.52  
% 6.99/1.52  --instantiation_flag                    true
% 6.99/1.52  --inst_sos_flag                         false
% 6.99/1.52  --inst_sos_phase                        true
% 6.99/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.99/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.99/1.52  --inst_lit_sel_side                     none
% 6.99/1.52  --inst_solver_per_active                1400
% 6.99/1.52  --inst_solver_calls_frac                1.
% 6.99/1.52  --inst_passive_queue_type               priority_queues
% 6.99/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.99/1.52  --inst_passive_queues_freq              [25;2]
% 6.99/1.52  --inst_dismatching                      true
% 6.99/1.52  --inst_eager_unprocessed_to_passive     true
% 6.99/1.52  --inst_prop_sim_given                   true
% 6.99/1.52  --inst_prop_sim_new                     false
% 6.99/1.52  --inst_subs_new                         false
% 6.99/1.52  --inst_eq_res_simp                      false
% 6.99/1.52  --inst_subs_given                       false
% 6.99/1.52  --inst_orphan_elimination               true
% 6.99/1.52  --inst_learning_loop_flag               true
% 6.99/1.52  --inst_learning_start                   3000
% 6.99/1.52  --inst_learning_factor                  2
% 6.99/1.52  --inst_start_prop_sim_after_learn       3
% 6.99/1.52  --inst_sel_renew                        solver
% 6.99/1.52  --inst_lit_activity_flag                true
% 6.99/1.52  --inst_restr_to_given                   false
% 6.99/1.52  --inst_activity_threshold               500
% 6.99/1.52  --inst_out_proof                        true
% 6.99/1.52  
% 6.99/1.52  ------ Resolution Options
% 6.99/1.52  
% 6.99/1.52  --resolution_flag                       false
% 6.99/1.52  --res_lit_sel                           adaptive
% 6.99/1.52  --res_lit_sel_side                      none
% 6.99/1.52  --res_ordering                          kbo
% 6.99/1.52  --res_to_prop_solver                    active
% 6.99/1.52  --res_prop_simpl_new                    false
% 6.99/1.52  --res_prop_simpl_given                  true
% 6.99/1.52  --res_passive_queue_type                priority_queues
% 6.99/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.99/1.52  --res_passive_queues_freq               [15;5]
% 6.99/1.52  --res_forward_subs                      full
% 6.99/1.52  --res_backward_subs                     full
% 6.99/1.52  --res_forward_subs_resolution           true
% 6.99/1.52  --res_backward_subs_resolution          true
% 6.99/1.52  --res_orphan_elimination                true
% 6.99/1.52  --res_time_limit                        2.
% 6.99/1.52  --res_out_proof                         true
% 6.99/1.52  
% 6.99/1.52  ------ Superposition Options
% 6.99/1.52  
% 6.99/1.52  --superposition_flag                    true
% 6.99/1.52  --sup_passive_queue_type                priority_queues
% 6.99/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.99/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.99/1.52  --demod_completeness_check              fast
% 6.99/1.52  --demod_use_ground                      true
% 6.99/1.52  --sup_to_prop_solver                    passive
% 6.99/1.52  --sup_prop_simpl_new                    true
% 6.99/1.52  --sup_prop_simpl_given                  true
% 6.99/1.52  --sup_fun_splitting                     false
% 6.99/1.52  --sup_smt_interval                      50000
% 6.99/1.52  
% 6.99/1.52  ------ Superposition Simplification Setup
% 6.99/1.52  
% 6.99/1.52  --sup_indices_passive                   []
% 6.99/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.99/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.52  --sup_full_bw                           [BwDemod]
% 6.99/1.52  --sup_immed_triv                        [TrivRules]
% 6.99/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.99/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.52  --sup_immed_bw_main                     []
% 6.99/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.99/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.52  
% 6.99/1.52  ------ Combination Options
% 6.99/1.52  
% 6.99/1.52  --comb_res_mult                         3
% 6.99/1.52  --comb_sup_mult                         2
% 6.99/1.52  --comb_inst_mult                        10
% 6.99/1.52  
% 6.99/1.52  ------ Debug Options
% 6.99/1.52  
% 6.99/1.52  --dbg_backtrace                         false
% 6.99/1.52  --dbg_dump_prop_clauses                 false
% 6.99/1.52  --dbg_dump_prop_clauses_file            -
% 6.99/1.52  --dbg_out_stat                          false
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  ------ Proving...
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  % SZS status Theorem for theBenchmark.p
% 6.99/1.52  
% 6.99/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 6.99/1.52  
% 6.99/1.52  fof(f25,conjecture,(
% 6.99/1.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f26,negated_conjecture,(
% 6.99/1.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.99/1.52    inference(negated_conjecture,[],[f25])).
% 6.99/1.52  
% 6.99/1.52  fof(f59,plain,(
% 6.99/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.99/1.52    inference(ennf_transformation,[],[f26])).
% 6.99/1.52  
% 6.99/1.52  fof(f60,plain,(
% 6.99/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.99/1.52    inference(flattening,[],[f59])).
% 6.99/1.52  
% 6.99/1.52  fof(f75,plain,(
% 6.99/1.52    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 6.99/1.52    introduced(choice_axiom,[])).
% 6.99/1.52  
% 6.99/1.52  fof(f74,plain,(
% 6.99/1.52    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 6.99/1.52    introduced(choice_axiom,[])).
% 6.99/1.52  
% 6.99/1.52  fof(f73,plain,(
% 6.99/1.52    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 6.99/1.52    introduced(choice_axiom,[])).
% 6.99/1.52  
% 6.99/1.52  fof(f72,plain,(
% 6.99/1.52    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 6.99/1.52    introduced(choice_axiom,[])).
% 6.99/1.52  
% 6.99/1.52  fof(f71,plain,(
% 6.99/1.52    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 6.99/1.52    introduced(choice_axiom,[])).
% 6.99/1.52  
% 6.99/1.52  fof(f70,plain,(
% 6.99/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 6.99/1.52    introduced(choice_axiom,[])).
% 6.99/1.52  
% 6.99/1.52  fof(f76,plain,(
% 6.99/1.52    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 6.99/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f60,f75,f74,f73,f72,f71,f70])).
% 6.99/1.52  
% 6.99/1.52  fof(f117,plain,(
% 6.99/1.52    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f3,axiom,(
% 6.99/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f31,plain,(
% 6.99/1.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.99/1.52    inference(ennf_transformation,[],[f3])).
% 6.99/1.52  
% 6.99/1.52  fof(f80,plain,(
% 6.99/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.99/1.52    inference(cnf_transformation,[],[f31])).
% 6.99/1.52  
% 6.99/1.52  fof(f5,axiom,(
% 6.99/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f82,plain,(
% 6.99/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.99/1.52    inference(cnf_transformation,[],[f5])).
% 6.99/1.52  
% 6.99/1.52  fof(f128,plain,(
% 6.99/1.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.99/1.52    inference(definition_unfolding,[],[f80,f82])).
% 6.99/1.52  
% 6.99/1.52  fof(f124,plain,(
% 6.99/1.52    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f22,axiom,(
% 6.99/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f53,plain,(
% 6.99/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.99/1.52    inference(ennf_transformation,[],[f22])).
% 6.99/1.52  
% 6.99/1.52  fof(f54,plain,(
% 6.99/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.99/1.52    inference(flattening,[],[f53])).
% 6.99/1.52  
% 6.99/1.52  fof(f105,plain,(
% 6.99/1.52    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f54])).
% 6.99/1.52  
% 6.99/1.52  fof(f122,plain,(
% 6.99/1.52    v1_funct_1(sK6)),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f121,plain,(
% 6.99/1.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f119,plain,(
% 6.99/1.52    v1_funct_1(sK5)),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f23,axiom,(
% 6.99/1.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f55,plain,(
% 6.99/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.99/1.52    inference(ennf_transformation,[],[f23])).
% 6.99/1.52  
% 6.99/1.52  fof(f56,plain,(
% 6.99/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.99/1.52    inference(flattening,[],[f55])).
% 6.99/1.52  
% 6.99/1.52  fof(f68,plain,(
% 6.99/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.99/1.52    inference(nnf_transformation,[],[f56])).
% 6.99/1.52  
% 6.99/1.52  fof(f69,plain,(
% 6.99/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.99/1.52    inference(flattening,[],[f68])).
% 6.99/1.52  
% 6.99/1.52  fof(f106,plain,(
% 6.99/1.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f69])).
% 6.99/1.52  
% 6.99/1.52  fof(f133,plain,(
% 6.99/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(equality_resolution,[],[f106])).
% 6.99/1.52  
% 6.99/1.52  fof(f24,axiom,(
% 6.99/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f57,plain,(
% 6.99/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.99/1.52    inference(ennf_transformation,[],[f24])).
% 6.99/1.52  
% 6.99/1.52  fof(f58,plain,(
% 6.99/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.99/1.52    inference(flattening,[],[f57])).
% 6.99/1.52  
% 6.99/1.52  fof(f109,plain,(
% 6.99/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f58])).
% 6.99/1.52  
% 6.99/1.52  fof(f110,plain,(
% 6.99/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f58])).
% 6.99/1.52  
% 6.99/1.52  fof(f111,plain,(
% 6.99/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f58])).
% 6.99/1.52  
% 6.99/1.52  fof(f4,axiom,(
% 6.99/1.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f32,plain,(
% 6.99/1.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 6.99/1.52    inference(ennf_transformation,[],[f4])).
% 6.99/1.52  
% 6.99/1.52  fof(f81,plain,(
% 6.99/1.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f32])).
% 6.99/1.52  
% 6.99/1.52  fof(f113,plain,(
% 6.99/1.52    ~v1_xboole_0(sK2)),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f114,plain,(
% 6.99/1.52    ~v1_xboole_0(sK3)),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f120,plain,(
% 6.99/1.52    v1_funct_2(sK5,sK3,sK2)),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f116,plain,(
% 6.99/1.52    ~v1_xboole_0(sK4)),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f123,plain,(
% 6.99/1.52    v1_funct_2(sK6,sK4,sK2)),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f16,axiom,(
% 6.99/1.52    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f44,plain,(
% 6.99/1.52    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.99/1.52    inference(ennf_transformation,[],[f16])).
% 6.99/1.52  
% 6.99/1.52  fof(f45,plain,(
% 6.99/1.52    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.99/1.52    inference(flattening,[],[f44])).
% 6.99/1.52  
% 6.99/1.52  fof(f64,plain,(
% 6.99/1.52    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.99/1.52    inference(nnf_transformation,[],[f45])).
% 6.99/1.52  
% 6.99/1.52  fof(f96,plain,(
% 6.99/1.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f64])).
% 6.99/1.52  
% 6.99/1.52  fof(f118,plain,(
% 6.99/1.52    r1_subset_1(sK3,sK4)),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f1,axiom,(
% 6.99/1.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f61,plain,(
% 6.99/1.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.99/1.52    inference(nnf_transformation,[],[f1])).
% 6.99/1.52  
% 6.99/1.52  fof(f77,plain,(
% 6.99/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f61])).
% 6.99/1.52  
% 6.99/1.52  fof(f127,plain,(
% 6.99/1.52    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 6.99/1.52    inference(definition_unfolding,[],[f77,f82])).
% 6.99/1.52  
% 6.99/1.52  fof(f17,axiom,(
% 6.99/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f46,plain,(
% 6.99/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.52    inference(ennf_transformation,[],[f17])).
% 6.99/1.52  
% 6.99/1.52  fof(f98,plain,(
% 6.99/1.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.52    inference(cnf_transformation,[],[f46])).
% 6.99/1.52  
% 6.99/1.52  fof(f20,axiom,(
% 6.99/1.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f49,plain,(
% 6.99/1.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 6.99/1.52    inference(ennf_transformation,[],[f20])).
% 6.99/1.52  
% 6.99/1.52  fof(f50,plain,(
% 6.99/1.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 6.99/1.52    inference(flattening,[],[f49])).
% 6.99/1.52  
% 6.99/1.52  fof(f102,plain,(
% 6.99/1.52    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f50])).
% 6.99/1.52  
% 6.99/1.52  fof(f18,axiom,(
% 6.99/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f28,plain,(
% 6.99/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.99/1.52    inference(pure_predicate_removal,[],[f18])).
% 6.99/1.52  
% 6.99/1.52  fof(f47,plain,(
% 6.99/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.52    inference(ennf_transformation,[],[f28])).
% 6.99/1.52  
% 6.99/1.52  fof(f99,plain,(
% 6.99/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.52    inference(cnf_transformation,[],[f47])).
% 6.99/1.52  
% 6.99/1.52  fof(f21,axiom,(
% 6.99/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f51,plain,(
% 6.99/1.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.99/1.52    inference(ennf_transformation,[],[f21])).
% 6.99/1.52  
% 6.99/1.52  fof(f52,plain,(
% 6.99/1.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.99/1.52    inference(flattening,[],[f51])).
% 6.99/1.52  
% 6.99/1.52  fof(f67,plain,(
% 6.99/1.52    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.99/1.52    inference(nnf_transformation,[],[f52])).
% 6.99/1.52  
% 6.99/1.52  fof(f103,plain,(
% 6.99/1.52    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f67])).
% 6.99/1.52  
% 6.99/1.52  fof(f10,axiom,(
% 6.99/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f38,plain,(
% 6.99/1.52    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 6.99/1.52    inference(ennf_transformation,[],[f10])).
% 6.99/1.52  
% 6.99/1.52  fof(f88,plain,(
% 6.99/1.52    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f38])).
% 6.99/1.52  
% 6.99/1.52  fof(f14,axiom,(
% 6.99/1.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f42,plain,(
% 6.99/1.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 6.99/1.52    inference(ennf_transformation,[],[f14])).
% 6.99/1.52  
% 6.99/1.52  fof(f94,plain,(
% 6.99/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f42])).
% 6.99/1.52  
% 6.99/1.52  fof(f12,axiom,(
% 6.99/1.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f90,plain,(
% 6.99/1.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.99/1.52    inference(cnf_transformation,[],[f12])).
% 6.99/1.52  
% 6.99/1.52  fof(f7,axiom,(
% 6.99/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f34,plain,(
% 6.99/1.52    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 6.99/1.52    inference(ennf_transformation,[],[f7])).
% 6.99/1.52  
% 6.99/1.52  fof(f35,plain,(
% 6.99/1.52    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 6.99/1.52    inference(flattening,[],[f34])).
% 6.99/1.52  
% 6.99/1.52  fof(f84,plain,(
% 6.99/1.52    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f35])).
% 6.99/1.52  
% 6.99/1.52  fof(f6,axiom,(
% 6.99/1.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f33,plain,(
% 6.99/1.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 6.99/1.52    inference(ennf_transformation,[],[f6])).
% 6.99/1.52  
% 6.99/1.52  fof(f83,plain,(
% 6.99/1.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f33])).
% 6.99/1.52  
% 6.99/1.52  fof(f15,axiom,(
% 6.99/1.52    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f43,plain,(
% 6.99/1.52    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 6.99/1.52    inference(ennf_transformation,[],[f15])).
% 6.99/1.52  
% 6.99/1.52  fof(f95,plain,(
% 6.99/1.52    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f43])).
% 6.99/1.52  
% 6.99/1.52  fof(f19,axiom,(
% 6.99/1.52    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f27,plain,(
% 6.99/1.52    ! [X0] : ~(! [X1] : ~r1_xboole_0(X1,X0) & k1_xboole_0 != X0)),
% 6.99/1.52    inference(pure_predicate_removal,[],[f19])).
% 6.99/1.52  
% 6.99/1.52  fof(f48,plain,(
% 6.99/1.52    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) | k1_xboole_0 = X0)),
% 6.99/1.52    inference(ennf_transformation,[],[f27])).
% 6.99/1.52  
% 6.99/1.52  fof(f65,plain,(
% 6.99/1.52    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) => r1_xboole_0(sK0(X0),X0))),
% 6.99/1.52    introduced(choice_axiom,[])).
% 6.99/1.52  
% 6.99/1.52  fof(f66,plain,(
% 6.99/1.52    ! [X0] : (r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0)),
% 6.99/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f65])).
% 6.99/1.52  
% 6.99/1.52  fof(f100,plain,(
% 6.99/1.52    ( ! [X0] : (r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 6.99/1.52    inference(cnf_transformation,[],[f66])).
% 6.99/1.52  
% 6.99/1.52  fof(f2,axiom,(
% 6.99/1.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f29,plain,(
% 6.99/1.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 6.99/1.52    inference(ennf_transformation,[],[f2])).
% 6.99/1.52  
% 6.99/1.52  fof(f30,plain,(
% 6.99/1.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 6.99/1.52    inference(flattening,[],[f29])).
% 6.99/1.52  
% 6.99/1.52  fof(f79,plain,(
% 6.99/1.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f30])).
% 6.99/1.52  
% 6.99/1.52  fof(f8,axiom,(
% 6.99/1.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f36,plain,(
% 6.99/1.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 6.99/1.52    inference(ennf_transformation,[],[f8])).
% 6.99/1.52  
% 6.99/1.52  fof(f85,plain,(
% 6.99/1.52    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f36])).
% 6.99/1.52  
% 6.99/1.52  fof(f91,plain,(
% 6.99/1.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 6.99/1.52    inference(cnf_transformation,[],[f12])).
% 6.99/1.52  
% 6.99/1.52  fof(f9,axiom,(
% 6.99/1.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 6.99/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.52  
% 6.99/1.52  fof(f37,plain,(
% 6.99/1.52    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.99/1.52    inference(ennf_transformation,[],[f9])).
% 6.99/1.52  
% 6.99/1.52  fof(f62,plain,(
% 6.99/1.52    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.99/1.52    inference(nnf_transformation,[],[f37])).
% 6.99/1.52  
% 6.99/1.52  fof(f86,plain,(
% 6.99/1.52    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f62])).
% 6.99/1.52  
% 6.99/1.52  fof(f107,plain,(
% 6.99/1.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f69])).
% 6.99/1.52  
% 6.99/1.52  fof(f132,plain,(
% 6.99/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(equality_resolution,[],[f107])).
% 6.99/1.52  
% 6.99/1.52  fof(f125,plain,(
% 6.99/1.52    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  fof(f115,plain,(
% 6.99/1.52    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 6.99/1.52    inference(cnf_transformation,[],[f76])).
% 6.99/1.52  
% 6.99/1.52  cnf(c_42,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 6.99/1.52      inference(cnf_transformation,[],[f117]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2534,plain,
% 6.99/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.99/1.52      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 6.99/1.52      inference(cnf_transformation,[],[f128]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2559,plain,
% 6.99/1.52      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 6.99/1.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4795,plain,
% 6.99/1.52      ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2534,c_2559]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_35,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 6.99/1.52      inference(cnf_transformation,[],[f124]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2540,plain,
% 6.99/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_27,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.99/1.52      inference(cnf_transformation,[],[f105]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2545,plain,
% 6.99/1.52      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 6.99/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.99/1.52      | v1_funct_1(X2) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_6834,plain,
% 6.99/1.52      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 6.99/1.52      | v1_funct_1(sK6) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2540,c_2545]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_37,negated_conjecture,
% 6.99/1.52      ( v1_funct_1(sK6) ),
% 6.99/1.52      inference(cnf_transformation,[],[f122]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3046,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.99/1.52      | ~ v1_funct_1(sK6)
% 6.99/1.52      | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_27]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3406,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 6.99/1.52      | ~ v1_funct_1(sK6)
% 6.99/1.52      | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_3046]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7054,plain,
% 6.99/1.52      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_6834,c_37,c_35,c_3406]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_38,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 6.99/1.52      inference(cnf_transformation,[],[f121]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2537,plain,
% 6.99/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_6835,plain,
% 6.99/1.52      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 6.99/1.52      | v1_funct_1(sK5) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2537,c_2545]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_40,negated_conjecture,
% 6.99/1.52      ( v1_funct_1(sK5) ),
% 6.99/1.52      inference(cnf_transformation,[],[f119]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3051,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.99/1.52      | ~ v1_funct_1(sK5)
% 6.99/1.52      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_27]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3411,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.99/1.52      | ~ v1_funct_1(sK5)
% 6.99/1.52      | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_3051]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7262,plain,
% 6.99/1.52      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_6835,c_40,c_38,c_3411]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_30,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.99/1.52      inference(cnf_transformation,[],[f133]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_33,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f109]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_32,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f110]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_31,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f111]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_258,plain,
% 6.99/1.52      ( ~ v1_funct_1(X3)
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_30,c_33,c_32,c_31]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_259,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_258]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2528,plain,
% 6.99/1.52      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 6.99/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.99/1.52      | v1_funct_2(X5,X4,X1) != iProver_top
% 6.99/1.52      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 6.99/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.99/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 6.99/1.52      | v1_funct_1(X2) != iProver_top
% 6.99/1.52      | v1_funct_1(X5) != iProver_top
% 6.99/1.52      | v1_xboole_0(X1) = iProver_top
% 6.99/1.52      | v1_xboole_0(X3) = iProver_top
% 6.99/1.52      | v1_xboole_0(X4) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.99/1.52      | ~ v1_xboole_0(X1)
% 6.99/1.52      | v1_xboole_0(X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f81]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2558,plain,
% 6.99/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.99/1.52      | v1_xboole_0(X1) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2823,plain,
% 6.99/1.52      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
% 6.99/1.52      | v1_funct_2(X5,X4,X1) != iProver_top
% 6.99/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 6.99/1.52      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 6.99/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 6.99/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.99/1.52      | v1_funct_1(X5) != iProver_top
% 6.99/1.52      | v1_funct_1(X2) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top
% 6.99/1.52      | v1_xboole_0(X1) = iProver_top
% 6.99/1.52      | v1_xboole_0(X4) = iProver_top ),
% 6.99/1.52      inference(forward_subsumption_resolution,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_2528,c_2558]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10535,plain,
% 6.99/1.52      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 6.99/1.52      | v1_funct_2(X1,X0,sK2) != iProver_top
% 6.99/1.52      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | v1_funct_1(X1) != iProver_top
% 6.99/1.52      | v1_funct_1(sK5) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK2) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_7262,c_2823]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_46,negated_conjecture,
% 6.99/1.52      ( ~ v1_xboole_0(sK2) ),
% 6.99/1.52      inference(cnf_transformation,[],[f113]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_49,plain,
% 6.99/1.52      ( v1_xboole_0(sK2) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_45,negated_conjecture,
% 6.99/1.52      ( ~ v1_xboole_0(sK3) ),
% 6.99/1.52      inference(cnf_transformation,[],[f114]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_50,plain,
% 6.99/1.52      ( v1_xboole_0(sK3) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_55,plain,
% 6.99/1.52      ( v1_funct_1(sK5) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_39,negated_conjecture,
% 6.99/1.52      ( v1_funct_2(sK5,sK3,sK2) ),
% 6.99/1.52      inference(cnf_transformation,[],[f120]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_56,plain,
% 6.99/1.52      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_57,plain,
% 6.99/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_12830,plain,
% 6.99/1.52      ( v1_funct_1(X1) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | v1_funct_2(X1,X0,sK2) != iProver_top
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 6.99/1.52      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_10535,c_49,c_50,c_55,c_56,c_57]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_12831,plain,
% 6.99/1.52      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 6.99/1.52      | v1_funct_2(X1,X0,sK2) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | v1_funct_1(X1) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_12830]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_12842,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 6.99/1.52      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 6.99/1.52      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 6.99/1.52      | v1_funct_1(sK6) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK4) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_7054,c_12831]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_43,negated_conjecture,
% 6.99/1.52      ( ~ v1_xboole_0(sK4) ),
% 6.99/1.52      inference(cnf_transformation,[],[f116]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_52,plain,
% 6.99/1.52      ( v1_xboole_0(sK4) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_58,plain,
% 6.99/1.52      ( v1_funct_1(sK6) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_36,negated_conjecture,
% 6.99/1.52      ( v1_funct_2(sK6,sK4,sK2) ),
% 6.99/1.52      inference(cnf_transformation,[],[f123]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_59,plain,
% 6.99/1.52      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_60,plain,
% 6.99/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_14801,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_12842,c_52,c_58,c_59,c_60]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_14811,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_4795,c_14801]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_19,plain,
% 6.99/1.52      ( ~ r1_subset_1(X0,X1)
% 6.99/1.52      | r1_xboole_0(X0,X1)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | v1_xboole_0(X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f96]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_41,negated_conjecture,
% 6.99/1.52      ( r1_subset_1(sK3,sK4) ),
% 6.99/1.52      inference(cnf_transformation,[],[f118]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_638,plain,
% 6.99/1.52      ( r1_xboole_0(X0,X1)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | v1_xboole_0(X0)
% 6.99/1.52      | sK4 != X1
% 6.99/1.52      | sK3 != X0 ),
% 6.99/1.52      inference(resolution_lifted,[status(thm)],[c_19,c_41]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_639,plain,
% 6.99/1.52      ( r1_xboole_0(sK3,sK4) | v1_xboole_0(sK4) | v1_xboole_0(sK3) ),
% 6.99/1.52      inference(unflattening,[status(thm)],[c_638]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_641,plain,
% 6.99/1.52      ( r1_xboole_0(sK3,sK4) ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_639,c_45,c_43]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2526,plain,
% 6.99/1.52      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1,plain,
% 6.99/1.52      ( ~ r1_xboole_0(X0,X1)
% 6.99/1.52      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f127]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2561,plain,
% 6.99/1.52      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 6.99/1.52      | r1_xboole_0(X0,X1) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3672,plain,
% 6.99/1.52      ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2526,c_2561]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_20,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | v1_relat_1(X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f98]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2547,plain,
% 6.99/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.99/1.52      | v1_relat_1(X0) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3887,plain,
% 6.99/1.52      ( v1_relat_1(sK6) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2540,c_2547]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_23,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | v1_partfun1(X0,X1)
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | v1_xboole_0(X2) ),
% 6.99/1.52      inference(cnf_transformation,[],[f102]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_21,plain,
% 6.99/1.52      ( v4_relat_1(X0,X1)
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.99/1.52      inference(cnf_transformation,[],[f99]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_26,plain,
% 6.99/1.52      ( ~ v1_partfun1(X0,X1)
% 6.99/1.52      | ~ v4_relat_1(X0,X1)
% 6.99/1.52      | ~ v1_relat_1(X0)
% 6.99/1.52      | k1_relat_1(X0) = X1 ),
% 6.99/1.52      inference(cnf_transformation,[],[f103]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_651,plain,
% 6.99/1.52      ( ~ v1_partfun1(X0,X1)
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ v1_relat_1(X0)
% 6.99/1.52      | k1_relat_1(X0) = X1 ),
% 6.99/1.52      inference(resolution,[status(thm)],[c_21,c_26]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_653,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ v1_partfun1(X0,X1)
% 6.99/1.52      | k1_relat_1(X0) = X1 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_651,c_26,c_21,c_20]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_654,plain,
% 6.99/1.52      ( ~ v1_partfun1(X0,X1)
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | k1_relat_1(X0) = X1 ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_653]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_711,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | k1_relat_1(X0) = X1 ),
% 6.99/1.52      inference(resolution,[status(thm)],[c_23,c_654]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_713,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | k1_relat_1(X0) = X1 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_711,c_26,c_23,c_21,c_20]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_714,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | k1_relat_1(X0) = X1 ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_713]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2524,plain,
% 6.99/1.52      ( k1_relat_1(X0) = X1
% 6.99/1.52      | v1_funct_2(X0,X1,X2) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.99/1.52      | v1_funct_1(X0) != iProver_top
% 6.99/1.52      | v1_xboole_0(X2) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3422,plain,
% 6.99/1.52      ( k1_relat_1(sK6) = sK4
% 6.99/1.52      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 6.99/1.52      | v1_funct_1(sK6) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2540,c_2524]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3563,plain,
% 6.99/1.52      ( k1_relat_1(sK6) = sK4 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_3422,c_49,c_58,c_59]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10,plain,
% 6.99/1.52      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 6.99/1.52      | ~ v1_relat_1(X1)
% 6.99/1.52      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f88]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2552,plain,
% 6.99/1.52      ( k7_relat_1(X0,X1) = k1_xboole_0
% 6.99/1.52      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 6.99/1.52      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5284,plain,
% 6.99/1.52      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 6.99/1.52      | r1_xboole_0(X0,sK4) != iProver_top
% 6.99/1.52      | v1_relat_1(sK6) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_3563,c_2552]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2968,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 6.99/1.52      | v1_relat_1(sK6) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_20]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2969,plain,
% 6.99/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 6.99/1.52      | v1_relat_1(sK6) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_2968]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7267,plain,
% 6.99/1.52      ( r1_xboole_0(X0,sK4) != iProver_top
% 6.99/1.52      | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_5284,c_60,c_2969]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7268,plain,
% 6.99/1.52      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 6.99/1.52      | r1_xboole_0(X0,sK4) != iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_7267]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7276,plain,
% 6.99/1.52      ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2526,c_7268]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_16,plain,
% 6.99/1.52      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f94]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2549,plain,
% 6.99/1.52      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 6.99/1.52      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7484,plain,
% 6.99/1.52      ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
% 6.99/1.52      | v1_relat_1(sK6) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_7276,c_2549]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_13,plain,
% 6.99/1.52      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f90]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7492,plain,
% 6.99/1.52      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 6.99/1.52      | v1_relat_1(sK6) != iProver_top ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_7484,c_13]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8127,plain,
% 6.99/1.52      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_7492,c_60,c_2969]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_6,plain,
% 6.99/1.52      ( ~ r1_tarski(X0,X1)
% 6.99/1.52      | ~ v1_relat_1(X2)
% 6.99/1.52      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f84]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2556,plain,
% 6.99/1.52      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
% 6.99/1.52      | r1_tarski(X2,X1) != iProver_top
% 6.99/1.52      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8132,plain,
% 6.99/1.52      ( k7_relat_1(k7_relat_1(X0,sK3),k1_xboole_0) = k7_relat_1(X0,k1_xboole_0)
% 6.99/1.52      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_8127,c_2556]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10154,plain,
% 6.99/1.52      ( k7_relat_1(k7_relat_1(sK6,sK3),k1_xboole_0) = k7_relat_1(sK6,k1_xboole_0) ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_3887,c_8132]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5,plain,
% 6.99/1.52      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 6.99/1.52      inference(cnf_transformation,[],[f83]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2557,plain,
% 6.99/1.52      ( v1_relat_1(X0) != iProver_top
% 6.99/1.52      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7485,plain,
% 6.99/1.52      ( v1_relat_1(sK6) != iProver_top
% 6.99/1.52      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_7276,c_2557]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8320,plain,
% 6.99/1.52      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_7485,c_60,c_2969]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17,plain,
% 6.99/1.52      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f95]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2548,plain,
% 6.99/1.52      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 6.99/1.52      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8326,plain,
% 6.99/1.52      ( k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_8320,c_2548]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8328,plain,
% 6.99/1.52      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_8326,c_13]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10159,plain,
% 6.99/1.52      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(light_normalisation,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_10154,c_7276,c_8328]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_14812,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(light_normalisation,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_14811,c_3672,c_10159]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_14813,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_14812,c_4795]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_22,plain,
% 6.99/1.52      ( r1_xboole_0(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f100]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2546,plain,
% 6.99/1.52      ( k1_xboole_0 = X0 | r1_xboole_0(sK0(X0),X0) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3418,plain,
% 6.99/1.52      ( k1_relat_1(sK5) = sK3
% 6.99/1.52      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 6.99/1.52      | v1_funct_1(sK5) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2537,c_2524]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3502,plain,
% 6.99/1.52      ( k1_relat_1(sK5) = sK3 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_3418,c_49,c_55,c_56]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5285,plain,
% 6.99/1.52      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 6.99/1.52      | r1_xboole_0(X0,sK3) != iProver_top
% 6.99/1.52      | v1_relat_1(sK5) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_3502,c_2552]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2971,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.99/1.52      | v1_relat_1(sK5) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_20]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2972,plain,
% 6.99/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 6.99/1.52      | v1_relat_1(sK5) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_2971]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7498,plain,
% 6.99/1.52      ( r1_xboole_0(X0,sK3) != iProver_top
% 6.99/1.52      | k7_relat_1(sK5,X0) = k1_xboole_0 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_5285,c_57,c_2972]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7499,plain,
% 6.99/1.52      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 6.99/1.52      | r1_xboole_0(X0,sK3) != iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_7498]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7506,plain,
% 6.99/1.52      ( k7_relat_1(sK5,sK0(sK3)) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2546,c_7499]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3888,plain,
% 6.99/1.52      ( v1_relat_1(sK5) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2537,c_2547]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9146,plain,
% 6.99/1.52      ( sK3 = k1_xboole_0
% 6.99/1.52      | r1_tarski(k1_relat_1(k1_xboole_0),sK0(sK3)) = iProver_top
% 6.99/1.52      | v1_relat_1(sK5) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_7506,c_2549]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9151,plain,
% 6.99/1.52      ( sK3 = k1_xboole_0
% 6.99/1.52      | r1_tarski(k1_xboole_0,sK0(sK3)) = iProver_top
% 6.99/1.52      | v1_relat_1(sK5) != iProver_top ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_9146,c_13]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2,plain,
% 6.99/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f79]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_142,plain,
% 6.99/1.52      ( r1_tarski(X0,X1) != iProver_top
% 6.99/1.52      | r1_xboole_0(X0,X1) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_144,plain,
% 6.99/1.52      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 6.99/1.52      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 6.99/1.52      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_142]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1587,plain,
% 6.99/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.99/1.52      theory(equality) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4216,plain,
% 6.99/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_1587]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4217,plain,
% 6.99/1.52      ( sK3 != X0
% 6.99/1.52      | v1_xboole_0(X0) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_4216]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4219,plain,
% 6.99/1.52      ( sK3 != k1_xboole_0
% 6.99/1.52      | v1_xboole_0(sK3) = iProver_top
% 6.99/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_4217]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9354,plain,
% 6.99/1.52      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 6.99/1.52      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_8328,c_2549]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9358,plain,
% 6.99/1.52      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 6.99/1.52      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_9354,c_13]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7,plain,
% 6.99/1.52      ( ~ v1_relat_1(X0)
% 6.99/1.52      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f85]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2555,plain,
% 6.99/1.52      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 6.99/1.52      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8325,plain,
% 6.99/1.52      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_8320,c_2555]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_12,plain,
% 6.99/1.52      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f91]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8331,plain,
% 6.99/1.52      ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_8325,c_12,c_13]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9,plain,
% 6.99/1.52      ( r1_xboole_0(k1_relat_1(X0),X1)
% 6.99/1.52      | ~ v1_relat_1(X0)
% 6.99/1.52      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f86]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2553,plain,
% 6.99/1.52      ( k9_relat_1(X0,X1) != k1_xboole_0
% 6.99/1.52      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 6.99/1.52      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9397,plain,
% 6.99/1.52      ( r1_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 6.99/1.52      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_8331,c_2553]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9398,plain,
% 6.99/1.52      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
% 6.99/1.52      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_9397,c_13]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10102,plain,
% 6.99/1.52      ( r1_tarski(k1_xboole_0,sK0(sK3)) = iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_9151,c_50,c_57,c_60,c_144,c_2969,c_2972,c_4219,c_7485,
% 6.99/1.52                 c_9358,c_9398]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10107,plain,
% 6.99/1.52      ( k7_relat_1(k7_relat_1(X0,sK0(sK3)),k1_xboole_0) = k7_relat_1(X0,k1_xboole_0)
% 6.99/1.52      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_10102,c_2556]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11518,plain,
% 6.99/1.52      ( k7_relat_1(k7_relat_1(sK5,sK0(sK3)),k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_3888,c_10107]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11601,plain,
% 6.99/1.52      ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0)
% 6.99/1.52      | sK3 = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_7506,c_11518]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11610,plain,
% 6.99/1.52      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_11601,c_8328]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_12115,plain,
% 6.99/1.52      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_11610,c_50,c_60,c_144,c_2969,c_4219,c_7485,c_9358,
% 6.99/1.52                 c_9398]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_14814,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 6.99/1.52      | k1_xboole_0 != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(light_normalisation,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_14813,c_3672,c_12115]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_14815,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(equality_resolution_simp,[status(thm)],[c_14814]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_29,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f132]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_265,plain,
% 6.99/1.52      ( ~ v1_funct_1(X3)
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_29,c_33,c_32,c_31]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_266,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_265]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2527,plain,
% 6.99/1.52      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 6.99/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.99/1.52      | v1_funct_2(X5,X4,X1) != iProver_top
% 6.99/1.52      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 6.99/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.99/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 6.99/1.52      | v1_funct_1(X2) != iProver_top
% 6.99/1.52      | v1_funct_1(X5) != iProver_top
% 6.99/1.52      | v1_xboole_0(X1) = iProver_top
% 6.99/1.52      | v1_xboole_0(X3) = iProver_top
% 6.99/1.52      | v1_xboole_0(X4) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2795,plain,
% 6.99/1.52      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
% 6.99/1.52      | v1_funct_2(X5,X4,X1) != iProver_top
% 6.99/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 6.99/1.52      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 6.99/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 6.99/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.99/1.52      | v1_funct_1(X5) != iProver_top
% 6.99/1.52      | v1_funct_1(X2) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top
% 6.99/1.52      | v1_xboole_0(X1) = iProver_top
% 6.99/1.52      | v1_xboole_0(X4) = iProver_top ),
% 6.99/1.52      inference(forward_subsumption_resolution,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_2527,c_2558]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9750,plain,
% 6.99/1.52      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 6.99/1.52      | v1_funct_2(X1,X0,sK2) != iProver_top
% 6.99/1.52      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | v1_funct_1(X1) != iProver_top
% 6.99/1.52      | v1_funct_1(sK5) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK2) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_7262,c_2795]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11005,plain,
% 6.99/1.52      ( v1_funct_1(X1) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | v1_funct_2(X1,X0,sK2) != iProver_top
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 6.99/1.52      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_9750,c_49,c_50,c_55,c_56,c_57]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11006,plain,
% 6.99/1.52      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 6.99/1.52      | v1_funct_2(X1,X0,sK2) != iProver_top
% 6.99/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 6.99/1.52      | v1_funct_1(X1) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_11005]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11017,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 6.99/1.52      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 6.99/1.52      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 6.99/1.52      | v1_funct_1(sK6) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK4) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_7054,c_11006]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11216,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_11017,c_52,c_58,c_59,c_60]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11226,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 6.99/1.52      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_4795,c_11216]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11227,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(light_normalisation,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_11226,c_3672,c_10159]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11228,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 6.99/1.52      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_11227,c_4795]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11229,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_11228,c_3672]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11230,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 6.99/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 6.99/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_11229]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_34,negated_conjecture,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 6.99/1.52      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 6.99/1.52      inference(cnf_transformation,[],[f125]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4810,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 6.99/1.52      | k2_partfun1(sK4,sK2,sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k2_partfun1(sK3,sK2,sK5,k1_setfam_1(k2_tarski(sK3,sK4))) ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_4795,c_34]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4811,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 6.99/1.52      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_4810,c_3672]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7058,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 6.99/1.52      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_7054,c_4811]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8461,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_7058,c_7262]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10824,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_10159,c_8461]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_53,plain,
% 6.99/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_44,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 6.99/1.52      inference(cnf_transformation,[],[f115]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_51,plain,
% 6.99/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(contradiction,plain,
% 6.99/1.52      ( $false ),
% 6.99/1.52      inference(minisat,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_14815,c_11610,c_11230,c_10824,c_9398,c_9358,c_7485,
% 6.99/1.52                 c_4219,c_2969,c_144,c_60,c_53,c_42,c_51,c_44,c_50]) ).
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 6.99/1.52  
% 6.99/1.52  ------                               Statistics
% 6.99/1.52  
% 6.99/1.52  ------ General
% 6.99/1.52  
% 6.99/1.52  abstr_ref_over_cycles:                  0
% 6.99/1.52  abstr_ref_under_cycles:                 0
% 6.99/1.52  gc_basic_clause_elim:                   0
% 6.99/1.52  forced_gc_time:                         0
% 6.99/1.52  parsing_time:                           0.024
% 6.99/1.52  unif_index_cands_time:                  0.
% 6.99/1.52  unif_index_add_time:                    0.
% 6.99/1.52  orderings_time:                         0.
% 6.99/1.52  out_proof_time:                         0.019
% 6.99/1.52  total_time:                             0.661
% 6.99/1.52  num_of_symbols:                         61
% 6.99/1.52  num_of_terms:                           24944
% 6.99/1.52  
% 6.99/1.52  ------ Preprocessing
% 6.99/1.52  
% 6.99/1.52  num_of_splits:                          0
% 6.99/1.52  num_of_split_atoms:                     0
% 6.99/1.52  num_of_reused_defs:                     0
% 6.99/1.52  num_eq_ax_congr_red:                    17
% 6.99/1.52  num_of_sem_filtered_clauses:            1
% 6.99/1.52  num_of_subtypes:                        0
% 6.99/1.52  monotx_restored_types:                  0
% 6.99/1.52  sat_num_of_epr_types:                   0
% 6.99/1.52  sat_num_of_non_cyclic_types:            0
% 6.99/1.52  sat_guarded_non_collapsed_types:        0
% 6.99/1.52  num_pure_diseq_elim:                    0
% 6.99/1.52  simp_replaced_by:                       0
% 6.99/1.52  res_preprocessed:                       214
% 6.99/1.52  prep_upred:                             0
% 6.99/1.52  prep_unflattend:                        60
% 6.99/1.52  smt_new_axioms:                         0
% 6.99/1.52  pred_elim_cands:                        7
% 6.99/1.52  pred_elim:                              3
% 6.99/1.52  pred_elim_cl:                           5
% 6.99/1.52  pred_elim_cycles:                       7
% 6.99/1.52  merged_defs:                            8
% 6.99/1.52  merged_defs_ncl:                        0
% 6.99/1.52  bin_hyper_res:                          8
% 6.99/1.52  prep_cycles:                            4
% 6.99/1.52  pred_elim_time:                         0.013
% 6.99/1.52  splitting_time:                         0.
% 6.99/1.52  sem_filter_time:                        0.
% 6.99/1.52  monotx_time:                            0.001
% 6.99/1.52  subtype_inf_time:                       0.
% 6.99/1.52  
% 6.99/1.52  ------ Problem properties
% 6.99/1.52  
% 6.99/1.52  clauses:                                42
% 6.99/1.52  conjectures:                            13
% 6.99/1.52  epr:                                    10
% 6.99/1.52  horn:                                   34
% 6.99/1.52  ground:                                 16
% 6.99/1.52  unary:                                  15
% 6.99/1.52  binary:                                 10
% 6.99/1.52  lits:                                   154
% 6.99/1.52  lits_eq:                                28
% 6.99/1.52  fd_pure:                                0
% 6.99/1.52  fd_pseudo:                              0
% 6.99/1.52  fd_cond:                                1
% 6.99/1.52  fd_pseudo_cond:                         1
% 6.99/1.52  ac_symbols:                             0
% 6.99/1.52  
% 6.99/1.52  ------ Propositional Solver
% 6.99/1.52  
% 6.99/1.52  prop_solver_calls:                      27
% 6.99/1.52  prop_fast_solver_calls:                 2564
% 6.99/1.52  smt_solver_calls:                       0
% 6.99/1.52  smt_fast_solver_calls:                  0
% 6.99/1.52  prop_num_of_clauses:                    4951
% 6.99/1.52  prop_preprocess_simplified:             13131
% 6.99/1.52  prop_fo_subsumed:                       151
% 6.99/1.52  prop_solver_time:                       0.
% 6.99/1.52  smt_solver_time:                        0.
% 6.99/1.52  smt_fast_solver_time:                   0.
% 6.99/1.52  prop_fast_solver_time:                  0.
% 6.99/1.52  prop_unsat_core_time:                   0.
% 6.99/1.52  
% 6.99/1.52  ------ QBF
% 6.99/1.52  
% 6.99/1.52  qbf_q_res:                              0
% 6.99/1.52  qbf_num_tautologies:                    0
% 6.99/1.52  qbf_prep_cycles:                        0
% 6.99/1.52  
% 6.99/1.52  ------ BMC1
% 6.99/1.52  
% 6.99/1.52  bmc1_current_bound:                     -1
% 6.99/1.52  bmc1_last_solved_bound:                 -1
% 6.99/1.52  bmc1_unsat_core_size:                   -1
% 6.99/1.52  bmc1_unsat_core_parents_size:           -1
% 6.99/1.52  bmc1_merge_next_fun:                    0
% 6.99/1.52  bmc1_unsat_core_clauses_time:           0.
% 6.99/1.52  
% 6.99/1.52  ------ Instantiation
% 6.99/1.52  
% 6.99/1.52  inst_num_of_clauses:                    1179
% 6.99/1.52  inst_num_in_passive:                    378
% 6.99/1.52  inst_num_in_active:                     682
% 6.99/1.52  inst_num_in_unprocessed:                119
% 6.99/1.52  inst_num_of_loops:                      910
% 6.99/1.52  inst_num_of_learning_restarts:          0
% 6.99/1.52  inst_num_moves_active_passive:          226
% 6.99/1.52  inst_lit_activity:                      0
% 6.99/1.52  inst_lit_activity_moves:                0
% 6.99/1.52  inst_num_tautologies:                   0
% 6.99/1.52  inst_num_prop_implied:                  0
% 6.99/1.52  inst_num_existing_simplified:           0
% 6.99/1.52  inst_num_eq_res_simplified:             0
% 6.99/1.52  inst_num_child_elim:                    0
% 6.99/1.52  inst_num_of_dismatching_blockings:      1039
% 6.99/1.52  inst_num_of_non_proper_insts:           1574
% 6.99/1.52  inst_num_of_duplicates:                 0
% 6.99/1.52  inst_inst_num_from_inst_to_res:         0
% 6.99/1.52  inst_dismatching_checking_time:         0.
% 6.99/1.52  
% 6.99/1.52  ------ Resolution
% 6.99/1.52  
% 6.99/1.52  res_num_of_clauses:                     0
% 6.99/1.52  res_num_in_passive:                     0
% 6.99/1.52  res_num_in_active:                      0
% 6.99/1.52  res_num_of_loops:                       218
% 6.99/1.52  res_forward_subset_subsumed:            29
% 6.99/1.52  res_backward_subset_subsumed:           0
% 6.99/1.52  res_forward_subsumed:                   0
% 6.99/1.52  res_backward_subsumed:                  0
% 6.99/1.52  res_forward_subsumption_resolution:     1
% 6.99/1.52  res_backward_subsumption_resolution:    0
% 6.99/1.52  res_clause_to_clause_subsumption:       993
% 6.99/1.52  res_orphan_elimination:                 0
% 6.99/1.52  res_tautology_del:                      37
% 6.99/1.52  res_num_eq_res_simplified:              0
% 6.99/1.52  res_num_sel_changes:                    0
% 6.99/1.52  res_moves_from_active_to_pass:          0
% 6.99/1.52  
% 6.99/1.52  ------ Superposition
% 6.99/1.52  
% 6.99/1.52  sup_time_total:                         0.
% 6.99/1.52  sup_time_generating:                    0.
% 6.99/1.52  sup_time_sim_full:                      0.
% 6.99/1.52  sup_time_sim_immed:                     0.
% 6.99/1.52  
% 6.99/1.52  sup_num_of_clauses:                     287
% 6.99/1.52  sup_num_in_active:                      174
% 6.99/1.52  sup_num_in_passive:                     113
% 6.99/1.52  sup_num_of_loops:                       181
% 6.99/1.52  sup_fw_superposition:                   258
% 6.99/1.52  sup_bw_superposition:                   149
% 6.99/1.52  sup_immediate_simplified:               221
% 6.99/1.52  sup_given_eliminated:                   0
% 6.99/1.52  comparisons_done:                       0
% 6.99/1.52  comparisons_avoided:                    0
% 6.99/1.52  
% 6.99/1.52  ------ Simplifications
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  sim_fw_subset_subsumed:                 30
% 6.99/1.52  sim_bw_subset_subsumed:                 4
% 6.99/1.52  sim_fw_subsumed:                        18
% 6.99/1.52  sim_bw_subsumed:                        0
% 6.99/1.52  sim_fw_subsumption_res:                 6
% 6.99/1.52  sim_bw_subsumption_res:                 0
% 6.99/1.52  sim_tautology_del:                      19
% 6.99/1.52  sim_eq_tautology_del:                   37
% 6.99/1.52  sim_eq_res_simp:                        1
% 6.99/1.52  sim_fw_demodulated:                     71
% 6.99/1.52  sim_bw_demodulated:                     6
% 6.99/1.52  sim_light_normalised:                   128
% 6.99/1.52  sim_joinable_taut:                      0
% 6.99/1.52  sim_joinable_simp:                      0
% 6.99/1.52  sim_ac_normalised:                      0
% 6.99/1.52  sim_smt_subsumption:                    0
% 6.99/1.52  
%------------------------------------------------------------------------------
