%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:38 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :  240 (3116 expanded)
%              Number of clauses        :  163 ( 847 expanded)
%              Number of leaves         :   20 (1176 expanded)
%              Depth                    :   29
%              Number of atoms          : 1320 (38568 expanded)
%              Number of equality atoms :  561 (9207 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f45,f44,f43,f42,f41,f40])).

fof(f80,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
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

fof(f14,plain,(
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

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f63])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1228,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2068,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1228])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1235,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2062,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_3414,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2068,c_2062])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1242,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2055,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1240,plain,
    ( r1_xboole_0(X0_54,X1_54)
    | r2_hidden(sK1(X0_54,X1_54),X1_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2057,plain,
    ( r1_xboole_0(X0_54,X1_54) = iProver_top
    | r2_hidden(sK1(X0_54,X1_54),X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1245,plain,
    ( ~ r2_hidden(X0_56,X0_54)
    | ~ v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2052,plain,
    ( r2_hidden(X0_56,X0_54) != iProver_top
    | v1_xboole_0(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_3354,plain,
    ( r1_xboole_0(X0_54,X1_54) = iProver_top
    | v1_xboole_0(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_2052])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1243,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | k3_xboole_0(X0_54,X1_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2054,plain,
    ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(X0_54,X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1243])).

cnf(c_3663,plain,
    ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
    | v1_xboole_0(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3354,c_2054])).

cnf(c_5353,plain,
    ( k3_xboole_0(X0_54,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2055,c_3663])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1244,plain,
    ( r1_xboole_0(X0_54,X1_54)
    | k3_xboole_0(X0_54,X1_54) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2053,plain,
    ( k3_xboole_0(X0_54,X1_54) != k1_xboole_0
    | r1_xboole_0(X0_54,X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_6261,plain,
    ( r1_xboole_0(X0_54,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5353,c_2053])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1237,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_54),X1_54)
    | ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,X1_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2060,plain,
    ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_54),X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_6267,plain,
    ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_6261,c_2060])).

cnf(c_7647,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3414,c_6267])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1234,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2063,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1234])).

cnf(c_3680,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2068,c_2063])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2507,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0_54,X1_54,sK7,X2_54) = k7_relat_1(sK7,X2_54) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2708,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54) ),
    inference(instantiation,[status(thm)],[c_2507])).

cnf(c_3955,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3680,c_24,c_22,c_2708])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1222,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2074,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1222])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1238,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2059,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_3337,plain,
    ( k9_subset_1(sK2,X0_54,sK5) = k3_xboole_0(X0_54,sK5) ),
    inference(superposition,[status(thm)],[c_2074,c_2059])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1229,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3512,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_3337,c_1229])).

cnf(c_12,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_487,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_488,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_490,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_32,c_30])).

cnf(c_1214,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_490])).

cnf(c_2082,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1214])).

cnf(c_2951,plain,
    ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2082,c_2054])).

cnf(c_3513,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3512,c_2951])).

cnf(c_3959,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3955,c_3513])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1225,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2071,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1225])).

cnf(c_3681,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2071,c_2063])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2512,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0_54,X1_54,sK6,X2_54) = k7_relat_1(sK6,X2_54) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2713,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54) ),
    inference(instantiation,[status(thm)],[c_2512])).

cnf(c_3961,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3681,c_27,c_25,c_2713])).

cnf(c_4087,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3959,c_3961])).

cnf(c_7878,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7647,c_4087])).

cnf(c_2428,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_2643,plain,
    ( r1_xboole_0(X0_54,k1_xboole_0)
    | r2_hidden(sK1(X0_54,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_2990,plain,
    ( r1_xboole_0(k1_relat_1(sK6),k1_xboole_0)
    | r2_hidden(sK1(k1_relat_1(sK6),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2643])).

cnf(c_2619,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK6),X0_54)
    | ~ v1_relat_1(sK6)
    | k7_relat_1(sK6,X0_54) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_2991,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK6),k1_xboole_0)
    | ~ v1_relat_1(sK6)
    | k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2619])).

cnf(c_2416,plain,
    ( ~ r2_hidden(X0_56,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_2642,plain,
    ( ~ r2_hidden(sK1(X0_54,k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_3881,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(sK6),k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2642])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f85])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_188,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_20,c_19,c_18])).

cnf(c_189,plain,
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
    inference(renaming,[status(thm)],[c_188])).

cnf(c_1216,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_189])).

cnf(c_2080,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
    | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_5865,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3955,c_2080])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_39,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_45,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6365,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
    | k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5865,c_36,c_39,c_45,c_46,c_47])).

cnf(c_6366,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6365])).

cnf(c_6381,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3961,c_6366])).

cnf(c_37,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6473,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6381,c_37,c_42,c_43,c_44])).

cnf(c_6474,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6473])).

cnf(c_6484,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3337,c_6474])).

cnf(c_6485,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6484,c_2951])).

cnf(c_6486,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6485,c_3337])).

cnf(c_6487,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6486,c_2951])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6488,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6487])).

cnf(c_18128,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6487,c_34,c_31,c_29,c_6488])).

cnf(c_18129,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_18128])).

cnf(c_3415,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2071,c_2062])).

cnf(c_7648,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3415,c_6267])).

cnf(c_18130,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18129,c_7647,c_7648])).

cnf(c_18131,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_18130])).

cnf(c_19281,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7878,c_25,c_4,c_2428,c_2990,c_2991,c_3881,c_18131])).

cnf(c_1232,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2065,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_xboole_0(X5_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_5135,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_2065,c_2063])).

cnf(c_1230,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2067,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
    | v1_xboole_0(X5_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_11677,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5135,c_2067])).

cnf(c_11681,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
    | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2068,c_11677])).

cnf(c_12046,plain,
    ( v1_funct_1(X2_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
    | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11681,c_36,c_39,c_45,c_46])).

cnf(c_12047,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
    | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_12046])).

cnf(c_12061,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2071,c_12047])).

cnf(c_12445,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12061,c_37,c_42,c_43])).

cnf(c_12446,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_12445])).

cnf(c_12455,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54)
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2074,c_12446])).

cnf(c_35,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12506,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12455,c_35,c_38])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f84])).

cnf(c_195,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_20,c_19,c_18])).

cnf(c_196,plain,
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
    inference(renaming,[status(thm)],[c_195])).

cnf(c_1215,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_196])).

cnf(c_2081,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
    | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_7100,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3955,c_2081])).

cnf(c_14733,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7100,c_36,c_39,c_45,c_46,c_47])).

cnf(c_14734,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_14733])).

cnf(c_14754,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,X0_54,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3337,c_14734])).

cnf(c_14764,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14754,c_3337])).

cnf(c_40,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15147,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14764,c_35,c_40])).

cnf(c_15148,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_15147])).

cnf(c_15161,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3961,c_15148])).

cnf(c_15246,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15161,c_2951,c_7647,c_7648])).

cnf(c_15247,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15246])).

cnf(c_15248,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15247,c_12506])).

cnf(c_14749,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3961,c_14734])).

cnf(c_15083,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14749,c_37,c_42,c_43,c_44])).

cnf(c_15084,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_15083])).

cnf(c_15094,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3337,c_15084])).

cnf(c_15095,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15094,c_2951,c_7647])).

cnf(c_15096,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15095,c_3337,c_12506])).

cnf(c_15097,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15096,c_2951,c_7648])).

cnf(c_15098,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15097])).

cnf(c_15264,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15248,c_35,c_38,c_40,c_15098])).

cnf(c_19283,plain,
    ( sK7 != sK7 ),
    inference(demodulation,[status(thm)],[c_19281,c_12506,c_15264])).

cnf(c_19284,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19283])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.48/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/1.49  
% 7.48/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.48/1.49  
% 7.48/1.49  ------  iProver source info
% 7.48/1.49  
% 7.48/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.48/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.48/1.49  git: non_committed_changes: false
% 7.48/1.49  git: last_make_outside_of_git: false
% 7.48/1.49  
% 7.48/1.49  ------ 
% 7.48/1.49  
% 7.48/1.49  ------ Input Options
% 7.48/1.49  
% 7.48/1.49  --out_options                           all
% 7.48/1.49  --tptp_safe_out                         true
% 7.48/1.49  --problem_path                          ""
% 7.48/1.49  --include_path                          ""
% 7.48/1.49  --clausifier                            res/vclausify_rel
% 7.48/1.49  --clausifier_options                    --mode clausify
% 7.48/1.49  --stdin                                 false
% 7.48/1.49  --stats_out                             all
% 7.48/1.49  
% 7.48/1.49  ------ General Options
% 7.48/1.49  
% 7.48/1.49  --fof                                   false
% 7.48/1.49  --time_out_real                         305.
% 7.48/1.49  --time_out_virtual                      -1.
% 7.48/1.49  --symbol_type_check                     false
% 7.48/1.49  --clausify_out                          false
% 7.48/1.49  --sig_cnt_out                           false
% 7.48/1.49  --trig_cnt_out                          false
% 7.48/1.49  --trig_cnt_out_tolerance                1.
% 7.48/1.49  --trig_cnt_out_sk_spl                   false
% 7.48/1.49  --abstr_cl_out                          false
% 7.48/1.49  
% 7.48/1.49  ------ Global Options
% 7.48/1.49  
% 7.48/1.49  --schedule                              default
% 7.48/1.49  --add_important_lit                     false
% 7.48/1.49  --prop_solver_per_cl                    1000
% 7.48/1.49  --min_unsat_core                        false
% 7.48/1.49  --soft_assumptions                      false
% 7.48/1.49  --soft_lemma_size                       3
% 7.48/1.49  --prop_impl_unit_size                   0
% 7.48/1.49  --prop_impl_unit                        []
% 7.48/1.49  --share_sel_clauses                     true
% 7.48/1.49  --reset_solvers                         false
% 7.48/1.49  --bc_imp_inh                            [conj_cone]
% 7.48/1.49  --conj_cone_tolerance                   3.
% 7.48/1.49  --extra_neg_conj                        none
% 7.48/1.49  --large_theory_mode                     true
% 7.48/1.49  --prolific_symb_bound                   200
% 7.48/1.49  --lt_threshold                          2000
% 7.48/1.49  --clause_weak_htbl                      true
% 7.48/1.49  --gc_record_bc_elim                     false
% 7.48/1.49  
% 7.48/1.49  ------ Preprocessing Options
% 7.48/1.49  
% 7.48/1.49  --preprocessing_flag                    true
% 7.48/1.49  --time_out_prep_mult                    0.1
% 7.48/1.49  --splitting_mode                        input
% 7.48/1.49  --splitting_grd                         true
% 7.48/1.49  --splitting_cvd                         false
% 7.48/1.49  --splitting_cvd_svl                     false
% 7.48/1.49  --splitting_nvd                         32
% 7.48/1.49  --sub_typing                            true
% 7.48/1.49  --prep_gs_sim                           true
% 7.48/1.49  --prep_unflatten                        true
% 7.48/1.49  --prep_res_sim                          true
% 7.48/1.49  --prep_upred                            true
% 7.48/1.49  --prep_sem_filter                       exhaustive
% 7.48/1.49  --prep_sem_filter_out                   false
% 7.48/1.49  --pred_elim                             true
% 7.48/1.49  --res_sim_input                         true
% 7.48/1.49  --eq_ax_congr_red                       true
% 7.48/1.49  --pure_diseq_elim                       true
% 7.48/1.49  --brand_transform                       false
% 7.48/1.49  --non_eq_to_eq                          false
% 7.48/1.49  --prep_def_merge                        true
% 7.48/1.49  --prep_def_merge_prop_impl              false
% 7.48/1.49  --prep_def_merge_mbd                    true
% 7.48/1.49  --prep_def_merge_tr_red                 false
% 7.48/1.49  --prep_def_merge_tr_cl                  false
% 7.48/1.49  --smt_preprocessing                     true
% 7.48/1.49  --smt_ac_axioms                         fast
% 7.48/1.49  --preprocessed_out                      false
% 7.48/1.49  --preprocessed_stats                    false
% 7.48/1.49  
% 7.48/1.49  ------ Abstraction refinement Options
% 7.48/1.49  
% 7.48/1.49  --abstr_ref                             []
% 7.48/1.49  --abstr_ref_prep                        false
% 7.48/1.49  --abstr_ref_until_sat                   false
% 7.48/1.49  --abstr_ref_sig_restrict                funpre
% 7.48/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.48/1.49  --abstr_ref_under                       []
% 7.48/1.49  
% 7.48/1.49  ------ SAT Options
% 7.48/1.49  
% 7.48/1.49  --sat_mode                              false
% 7.48/1.49  --sat_fm_restart_options                ""
% 7.48/1.49  --sat_gr_def                            false
% 7.48/1.49  --sat_epr_types                         true
% 7.48/1.49  --sat_non_cyclic_types                  false
% 7.48/1.49  --sat_finite_models                     false
% 7.48/1.49  --sat_fm_lemmas                         false
% 7.48/1.49  --sat_fm_prep                           false
% 7.48/1.49  --sat_fm_uc_incr                        true
% 7.48/1.49  --sat_out_model                         small
% 7.48/1.49  --sat_out_clauses                       false
% 7.48/1.49  
% 7.48/1.49  ------ QBF Options
% 7.48/1.49  
% 7.48/1.49  --qbf_mode                              false
% 7.48/1.49  --qbf_elim_univ                         false
% 7.48/1.49  --qbf_dom_inst                          none
% 7.48/1.49  --qbf_dom_pre_inst                      false
% 7.48/1.49  --qbf_sk_in                             false
% 7.48/1.49  --qbf_pred_elim                         true
% 7.48/1.49  --qbf_split                             512
% 7.48/1.49  
% 7.48/1.49  ------ BMC1 Options
% 7.48/1.49  
% 7.48/1.49  --bmc1_incremental                      false
% 7.48/1.49  --bmc1_axioms                           reachable_all
% 7.48/1.49  --bmc1_min_bound                        0
% 7.48/1.49  --bmc1_max_bound                        -1
% 7.48/1.49  --bmc1_max_bound_default                -1
% 7.48/1.49  --bmc1_symbol_reachability              true
% 7.48/1.49  --bmc1_property_lemmas                  false
% 7.48/1.49  --bmc1_k_induction                      false
% 7.48/1.49  --bmc1_non_equiv_states                 false
% 7.48/1.49  --bmc1_deadlock                         false
% 7.48/1.49  --bmc1_ucm                              false
% 7.48/1.49  --bmc1_add_unsat_core                   none
% 7.48/1.49  --bmc1_unsat_core_children              false
% 7.48/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.48/1.49  --bmc1_out_stat                         full
% 7.48/1.49  --bmc1_ground_init                      false
% 7.48/1.49  --bmc1_pre_inst_next_state              false
% 7.48/1.49  --bmc1_pre_inst_state                   false
% 7.48/1.49  --bmc1_pre_inst_reach_state             false
% 7.48/1.49  --bmc1_out_unsat_core                   false
% 7.48/1.49  --bmc1_aig_witness_out                  false
% 7.48/1.49  --bmc1_verbose                          false
% 7.48/1.49  --bmc1_dump_clauses_tptp                false
% 7.48/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.48/1.49  --bmc1_dump_file                        -
% 7.48/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.48/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.48/1.49  --bmc1_ucm_extend_mode                  1
% 7.48/1.49  --bmc1_ucm_init_mode                    2
% 7.48/1.49  --bmc1_ucm_cone_mode                    none
% 7.48/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.48/1.49  --bmc1_ucm_relax_model                  4
% 7.48/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.48/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.48/1.49  --bmc1_ucm_layered_model                none
% 7.48/1.49  --bmc1_ucm_max_lemma_size               10
% 7.48/1.49  
% 7.48/1.49  ------ AIG Options
% 7.48/1.49  
% 7.48/1.49  --aig_mode                              false
% 7.48/1.49  
% 7.48/1.49  ------ Instantiation Options
% 7.48/1.49  
% 7.48/1.49  --instantiation_flag                    true
% 7.48/1.49  --inst_sos_flag                         false
% 7.48/1.49  --inst_sos_phase                        true
% 7.48/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.48/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.48/1.49  --inst_lit_sel_side                     num_symb
% 7.48/1.49  --inst_solver_per_active                1400
% 7.48/1.49  --inst_solver_calls_frac                1.
% 7.48/1.49  --inst_passive_queue_type               priority_queues
% 7.48/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.48/1.49  --inst_passive_queues_freq              [25;2]
% 7.48/1.49  --inst_dismatching                      true
% 7.48/1.49  --inst_eager_unprocessed_to_passive     true
% 7.48/1.49  --inst_prop_sim_given                   true
% 7.48/1.49  --inst_prop_sim_new                     false
% 7.48/1.49  --inst_subs_new                         false
% 7.48/1.49  --inst_eq_res_simp                      false
% 7.48/1.49  --inst_subs_given                       false
% 7.48/1.49  --inst_orphan_elimination               true
% 7.48/1.49  --inst_learning_loop_flag               true
% 7.48/1.49  --inst_learning_start                   3000
% 7.48/1.49  --inst_learning_factor                  2
% 7.48/1.49  --inst_start_prop_sim_after_learn       3
% 7.48/1.49  --inst_sel_renew                        solver
% 7.48/1.49  --inst_lit_activity_flag                true
% 7.48/1.49  --inst_restr_to_given                   false
% 7.48/1.49  --inst_activity_threshold               500
% 7.48/1.49  --inst_out_proof                        true
% 7.48/1.49  
% 7.48/1.49  ------ Resolution Options
% 7.48/1.49  
% 7.48/1.49  --resolution_flag                       true
% 7.48/1.49  --res_lit_sel                           adaptive
% 7.48/1.49  --res_lit_sel_side                      none
% 7.48/1.49  --res_ordering                          kbo
% 7.48/1.49  --res_to_prop_solver                    active
% 7.48/1.49  --res_prop_simpl_new                    false
% 7.48/1.49  --res_prop_simpl_given                  true
% 7.48/1.49  --res_passive_queue_type                priority_queues
% 7.48/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.48/1.49  --res_passive_queues_freq               [15;5]
% 7.48/1.49  --res_forward_subs                      full
% 7.48/1.49  --res_backward_subs                     full
% 7.48/1.49  --res_forward_subs_resolution           true
% 7.48/1.49  --res_backward_subs_resolution          true
% 7.48/1.49  --res_orphan_elimination                true
% 7.48/1.49  --res_time_limit                        2.
% 7.48/1.49  --res_out_proof                         true
% 7.48/1.49  
% 7.48/1.49  ------ Superposition Options
% 7.48/1.49  
% 7.48/1.49  --superposition_flag                    true
% 7.48/1.49  --sup_passive_queue_type                priority_queues
% 7.48/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.48/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.48/1.49  --demod_completeness_check              fast
% 7.48/1.49  --demod_use_ground                      true
% 7.48/1.49  --sup_to_prop_solver                    passive
% 7.48/1.49  --sup_prop_simpl_new                    true
% 7.48/1.49  --sup_prop_simpl_given                  true
% 7.48/1.49  --sup_fun_splitting                     false
% 7.48/1.49  --sup_smt_interval                      50000
% 7.48/1.49  
% 7.48/1.49  ------ Superposition Simplification Setup
% 7.48/1.49  
% 7.48/1.49  --sup_indices_passive                   []
% 7.48/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.48/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.49  --sup_full_bw                           [BwDemod]
% 7.48/1.49  --sup_immed_triv                        [TrivRules]
% 7.48/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.48/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.49  --sup_immed_bw_main                     []
% 7.48/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.48/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.49  
% 7.48/1.49  ------ Combination Options
% 7.48/1.49  
% 7.48/1.49  --comb_res_mult                         3
% 7.48/1.49  --comb_sup_mult                         2
% 7.48/1.49  --comb_inst_mult                        10
% 7.48/1.49  
% 7.48/1.49  ------ Debug Options
% 7.48/1.49  
% 7.48/1.49  --dbg_backtrace                         false
% 7.48/1.49  --dbg_dump_prop_clauses                 false
% 7.48/1.49  --dbg_dump_prop_clauses_file            -
% 7.48/1.49  --dbg_out_stat                          false
% 7.48/1.49  ------ Parsing...
% 7.48/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.48/1.49  
% 7.48/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.48/1.49  
% 7.48/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.48/1.49  
% 7.48/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.48/1.49  ------ Proving...
% 7.48/1.49  ------ Problem Properties 
% 7.48/1.49  
% 7.48/1.49  
% 7.48/1.49  clauses                                 33
% 7.48/1.49  conjectures                             13
% 7.48/1.49  EPR                                     12
% 7.48/1.49  Horn                                    24
% 7.48/1.49  unary                                   14
% 7.48/1.49  binary                                  8
% 7.48/1.49  lits                                    129
% 7.48/1.49  lits eq                                 15
% 7.48/1.49  fd_pure                                 0
% 7.48/1.49  fd_pseudo                               0
% 7.48/1.49  fd_cond                                 0
% 7.48/1.49  fd_pseudo_cond                          0
% 7.48/1.49  AC symbols                              0
% 7.48/1.49  
% 7.48/1.49  ------ Schedule dynamic 5 is on 
% 7.48/1.49  
% 7.48/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.48/1.49  
% 7.48/1.49  
% 7.48/1.49  ------ 
% 7.48/1.49  Current options:
% 7.48/1.49  ------ 
% 7.48/1.49  
% 7.48/1.49  ------ Input Options
% 7.48/1.49  
% 7.48/1.49  --out_options                           all
% 7.48/1.49  --tptp_safe_out                         true
% 7.48/1.49  --problem_path                          ""
% 7.48/1.49  --include_path                          ""
% 7.48/1.49  --clausifier                            res/vclausify_rel
% 7.48/1.49  --clausifier_options                    --mode clausify
% 7.48/1.49  --stdin                                 false
% 7.48/1.49  --stats_out                             all
% 7.48/1.49  
% 7.48/1.49  ------ General Options
% 7.48/1.49  
% 7.48/1.49  --fof                                   false
% 7.48/1.49  --time_out_real                         305.
% 7.48/1.49  --time_out_virtual                      -1.
% 7.48/1.49  --symbol_type_check                     false
% 7.48/1.49  --clausify_out                          false
% 7.48/1.49  --sig_cnt_out                           false
% 7.48/1.49  --trig_cnt_out                          false
% 7.48/1.49  --trig_cnt_out_tolerance                1.
% 7.48/1.49  --trig_cnt_out_sk_spl                   false
% 7.48/1.49  --abstr_cl_out                          false
% 7.48/1.49  
% 7.48/1.49  ------ Global Options
% 7.48/1.49  
% 7.48/1.49  --schedule                              default
% 7.48/1.49  --add_important_lit                     false
% 7.48/1.49  --prop_solver_per_cl                    1000
% 7.48/1.49  --min_unsat_core                        false
% 7.48/1.49  --soft_assumptions                      false
% 7.48/1.49  --soft_lemma_size                       3
% 7.48/1.49  --prop_impl_unit_size                   0
% 7.48/1.49  --prop_impl_unit                        []
% 7.48/1.49  --share_sel_clauses                     true
% 7.48/1.49  --reset_solvers                         false
% 7.48/1.49  --bc_imp_inh                            [conj_cone]
% 7.48/1.49  --conj_cone_tolerance                   3.
% 7.48/1.49  --extra_neg_conj                        none
% 7.48/1.49  --large_theory_mode                     true
% 7.48/1.49  --prolific_symb_bound                   200
% 7.48/1.49  --lt_threshold                          2000
% 7.48/1.49  --clause_weak_htbl                      true
% 7.48/1.49  --gc_record_bc_elim                     false
% 7.48/1.49  
% 7.48/1.49  ------ Preprocessing Options
% 7.48/1.49  
% 7.48/1.49  --preprocessing_flag                    true
% 7.48/1.49  --time_out_prep_mult                    0.1
% 7.48/1.49  --splitting_mode                        input
% 7.48/1.49  --splitting_grd                         true
% 7.48/1.49  --splitting_cvd                         false
% 7.48/1.49  --splitting_cvd_svl                     false
% 7.48/1.49  --splitting_nvd                         32
% 7.48/1.49  --sub_typing                            true
% 7.48/1.49  --prep_gs_sim                           true
% 7.48/1.49  --prep_unflatten                        true
% 7.48/1.49  --prep_res_sim                          true
% 7.48/1.49  --prep_upred                            true
% 7.48/1.49  --prep_sem_filter                       exhaustive
% 7.48/1.49  --prep_sem_filter_out                   false
% 7.48/1.49  --pred_elim                             true
% 7.48/1.49  --res_sim_input                         true
% 7.48/1.49  --eq_ax_congr_red                       true
% 7.48/1.49  --pure_diseq_elim                       true
% 7.48/1.49  --brand_transform                       false
% 7.48/1.49  --non_eq_to_eq                          false
% 7.48/1.49  --prep_def_merge                        true
% 7.48/1.49  --prep_def_merge_prop_impl              false
% 7.48/1.49  --prep_def_merge_mbd                    true
% 7.48/1.49  --prep_def_merge_tr_red                 false
% 7.48/1.49  --prep_def_merge_tr_cl                  false
% 7.48/1.49  --smt_preprocessing                     true
% 7.48/1.49  --smt_ac_axioms                         fast
% 7.48/1.49  --preprocessed_out                      false
% 7.48/1.49  --preprocessed_stats                    false
% 7.48/1.49  
% 7.48/1.49  ------ Abstraction refinement Options
% 7.48/1.49  
% 7.48/1.49  --abstr_ref                             []
% 7.48/1.49  --abstr_ref_prep                        false
% 7.48/1.49  --abstr_ref_until_sat                   false
% 7.48/1.49  --abstr_ref_sig_restrict                funpre
% 7.48/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.48/1.49  --abstr_ref_under                       []
% 7.48/1.49  
% 7.48/1.49  ------ SAT Options
% 7.48/1.49  
% 7.48/1.49  --sat_mode                              false
% 7.48/1.49  --sat_fm_restart_options                ""
% 7.48/1.49  --sat_gr_def                            false
% 7.48/1.49  --sat_epr_types                         true
% 7.48/1.49  --sat_non_cyclic_types                  false
% 7.48/1.49  --sat_finite_models                     false
% 7.48/1.49  --sat_fm_lemmas                         false
% 7.48/1.49  --sat_fm_prep                           false
% 7.48/1.49  --sat_fm_uc_incr                        true
% 7.48/1.49  --sat_out_model                         small
% 7.48/1.49  --sat_out_clauses                       false
% 7.48/1.49  
% 7.48/1.49  ------ QBF Options
% 7.48/1.49  
% 7.48/1.49  --qbf_mode                              false
% 7.48/1.49  --qbf_elim_univ                         false
% 7.48/1.49  --qbf_dom_inst                          none
% 7.48/1.49  --qbf_dom_pre_inst                      false
% 7.48/1.49  --qbf_sk_in                             false
% 7.48/1.49  --qbf_pred_elim                         true
% 7.48/1.49  --qbf_split                             512
% 7.48/1.49  
% 7.48/1.49  ------ BMC1 Options
% 7.48/1.49  
% 7.48/1.49  --bmc1_incremental                      false
% 7.48/1.49  --bmc1_axioms                           reachable_all
% 7.48/1.49  --bmc1_min_bound                        0
% 7.48/1.49  --bmc1_max_bound                        -1
% 7.48/1.49  --bmc1_max_bound_default                -1
% 7.48/1.49  --bmc1_symbol_reachability              true
% 7.48/1.49  --bmc1_property_lemmas                  false
% 7.48/1.49  --bmc1_k_induction                      false
% 7.48/1.49  --bmc1_non_equiv_states                 false
% 7.48/1.49  --bmc1_deadlock                         false
% 7.48/1.49  --bmc1_ucm                              false
% 7.48/1.49  --bmc1_add_unsat_core                   none
% 7.48/1.49  --bmc1_unsat_core_children              false
% 7.48/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.48/1.49  --bmc1_out_stat                         full
% 7.48/1.49  --bmc1_ground_init                      false
% 7.48/1.49  --bmc1_pre_inst_next_state              false
% 7.48/1.49  --bmc1_pre_inst_state                   false
% 7.48/1.49  --bmc1_pre_inst_reach_state             false
% 7.48/1.49  --bmc1_out_unsat_core                   false
% 7.48/1.49  --bmc1_aig_witness_out                  false
% 7.48/1.49  --bmc1_verbose                          false
% 7.48/1.49  --bmc1_dump_clauses_tptp                false
% 7.48/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.48/1.49  --bmc1_dump_file                        -
% 7.48/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.48/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.48/1.49  --bmc1_ucm_extend_mode                  1
% 7.48/1.49  --bmc1_ucm_init_mode                    2
% 7.48/1.49  --bmc1_ucm_cone_mode                    none
% 7.48/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.48/1.49  --bmc1_ucm_relax_model                  4
% 7.48/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.48/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.48/1.49  --bmc1_ucm_layered_model                none
% 7.48/1.49  --bmc1_ucm_max_lemma_size               10
% 7.48/1.49  
% 7.48/1.49  ------ AIG Options
% 7.48/1.49  
% 7.48/1.49  --aig_mode                              false
% 7.48/1.49  
% 7.48/1.49  ------ Instantiation Options
% 7.48/1.49  
% 7.48/1.49  --instantiation_flag                    true
% 7.48/1.49  --inst_sos_flag                         false
% 7.48/1.49  --inst_sos_phase                        true
% 7.48/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.48/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.48/1.49  --inst_lit_sel_side                     none
% 7.48/1.49  --inst_solver_per_active                1400
% 7.48/1.49  --inst_solver_calls_frac                1.
% 7.48/1.49  --inst_passive_queue_type               priority_queues
% 7.48/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.48/1.49  --inst_passive_queues_freq              [25;2]
% 7.48/1.49  --inst_dismatching                      true
% 7.48/1.49  --inst_eager_unprocessed_to_passive     true
% 7.48/1.49  --inst_prop_sim_given                   true
% 7.48/1.49  --inst_prop_sim_new                     false
% 7.48/1.49  --inst_subs_new                         false
% 7.48/1.49  --inst_eq_res_simp                      false
% 7.48/1.49  --inst_subs_given                       false
% 7.48/1.49  --inst_orphan_elimination               true
% 7.48/1.49  --inst_learning_loop_flag               true
% 7.48/1.49  --inst_learning_start                   3000
% 7.48/1.49  --inst_learning_factor                  2
% 7.48/1.49  --inst_start_prop_sim_after_learn       3
% 7.48/1.49  --inst_sel_renew                        solver
% 7.48/1.49  --inst_lit_activity_flag                true
% 7.48/1.49  --inst_restr_to_given                   false
% 7.48/1.49  --inst_activity_threshold               500
% 7.48/1.49  --inst_out_proof                        true
% 7.48/1.49  
% 7.48/1.49  ------ Resolution Options
% 7.48/1.49  
% 7.48/1.49  --resolution_flag                       false
% 7.48/1.49  --res_lit_sel                           adaptive
% 7.48/1.49  --res_lit_sel_side                      none
% 7.48/1.49  --res_ordering                          kbo
% 7.48/1.49  --res_to_prop_solver                    active
% 7.48/1.49  --res_prop_simpl_new                    false
% 7.48/1.49  --res_prop_simpl_given                  true
% 7.48/1.49  --res_passive_queue_type                priority_queues
% 7.48/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.48/1.49  --res_passive_queues_freq               [15;5]
% 7.48/1.49  --res_forward_subs                      full
% 7.48/1.49  --res_backward_subs                     full
% 7.48/1.49  --res_forward_subs_resolution           true
% 7.48/1.49  --res_backward_subs_resolution          true
% 7.48/1.49  --res_orphan_elimination                true
% 7.48/1.49  --res_time_limit                        2.
% 7.48/1.49  --res_out_proof                         true
% 7.48/1.49  
% 7.48/1.49  ------ Superposition Options
% 7.48/1.49  
% 7.48/1.49  --superposition_flag                    true
% 7.48/1.49  --sup_passive_queue_type                priority_queues
% 7.48/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.48/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.48/1.49  --demod_completeness_check              fast
% 7.48/1.49  --demod_use_ground                      true
% 7.48/1.49  --sup_to_prop_solver                    passive
% 7.48/1.49  --sup_prop_simpl_new                    true
% 7.48/1.49  --sup_prop_simpl_given                  true
% 7.48/1.49  --sup_fun_splitting                     false
% 7.48/1.49  --sup_smt_interval                      50000
% 7.48/1.49  
% 7.48/1.49  ------ Superposition Simplification Setup
% 7.48/1.49  
% 7.48/1.49  --sup_indices_passive                   []
% 7.48/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.48/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.49  --sup_full_bw                           [BwDemod]
% 7.48/1.49  --sup_immed_triv                        [TrivRules]
% 7.48/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.48/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.49  --sup_immed_bw_main                     []
% 7.48/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.48/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.49  
% 7.48/1.49  ------ Combination Options
% 7.48/1.49  
% 7.48/1.49  --comb_res_mult                         3
% 7.48/1.49  --comb_sup_mult                         2
% 7.48/1.49  --comb_inst_mult                        10
% 7.48/1.49  
% 7.48/1.49  ------ Debug Options
% 7.48/1.49  
% 7.48/1.49  --dbg_backtrace                         false
% 7.48/1.49  --dbg_dump_prop_clauses                 false
% 7.48/1.49  --dbg_dump_prop_clauses_file            -
% 7.48/1.49  --dbg_out_stat                          false
% 7.48/1.49  
% 7.48/1.49  
% 7.48/1.49  
% 7.48/1.49  
% 7.48/1.49  ------ Proving...
% 7.48/1.49  
% 7.48/1.49  
% 7.48/1.49  % SZS status Theorem for theBenchmark.p
% 7.48/1.49  
% 7.48/1.49   Resolution empty clause
% 7.48/1.49  
% 7.48/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.48/1.49  
% 7.48/1.49  fof(f12,conjecture,(
% 7.48/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f13,negated_conjecture,(
% 7.48/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.48/1.49    inference(negated_conjecture,[],[f12])).
% 7.48/1.49  
% 7.48/1.49  fof(f27,plain,(
% 7.48/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.48/1.49    inference(ennf_transformation,[],[f13])).
% 7.48/1.49  
% 7.48/1.49  fof(f28,plain,(
% 7.48/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.48/1.49    inference(flattening,[],[f27])).
% 7.48/1.49  
% 7.48/1.49  fof(f45,plain,(
% 7.48/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 7.48/1.49    introduced(choice_axiom,[])).
% 7.48/1.49  
% 7.48/1.49  fof(f44,plain,(
% 7.48/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 7.48/1.49    introduced(choice_axiom,[])).
% 7.48/1.49  
% 7.48/1.49  fof(f43,plain,(
% 7.48/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 7.48/1.49    introduced(choice_axiom,[])).
% 7.48/1.49  
% 7.48/1.49  fof(f42,plain,(
% 7.48/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.48/1.49    introduced(choice_axiom,[])).
% 7.48/1.49  
% 7.48/1.49  fof(f41,plain,(
% 7.48/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 7.48/1.49    introduced(choice_axiom,[])).
% 7.48/1.49  
% 7.48/1.49  fof(f40,plain,(
% 7.48/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 7.48/1.49    introduced(choice_axiom,[])).
% 7.48/1.49  
% 7.48/1.49  fof(f46,plain,(
% 7.48/1.49    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.48/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f45,f44,f43,f42,f41,f40])).
% 7.48/1.49  
% 7.48/1.49  fof(f80,plain,(
% 7.48/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f8,axiom,(
% 7.48/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f20,plain,(
% 7.48/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.48/1.49    inference(ennf_transformation,[],[f8])).
% 7.48/1.49  
% 7.48/1.49  fof(f60,plain,(
% 7.48/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.48/1.49    inference(cnf_transformation,[],[f20])).
% 7.48/1.49  
% 7.48/1.49  fof(f3,axiom,(
% 7.48/1.49    v1_xboole_0(k1_xboole_0)),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f51,plain,(
% 7.48/1.49    v1_xboole_0(k1_xboole_0)),
% 7.48/1.49    inference(cnf_transformation,[],[f3])).
% 7.48/1.49  
% 7.48/1.49  fof(f4,axiom,(
% 7.48/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f14,plain,(
% 7.48/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.48/1.49    inference(rectify,[],[f4])).
% 7.48/1.49  
% 7.48/1.49  fof(f15,plain,(
% 7.48/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.48/1.49    inference(ennf_transformation,[],[f14])).
% 7.48/1.49  
% 7.48/1.49  fof(f34,plain,(
% 7.48/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.48/1.49    introduced(choice_axiom,[])).
% 7.48/1.49  
% 7.48/1.49  fof(f35,plain,(
% 7.48/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.48/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f34])).
% 7.48/1.49  
% 7.48/1.49  fof(f53,plain,(
% 7.48/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f35])).
% 7.48/1.49  
% 7.48/1.49  fof(f1,axiom,(
% 7.48/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f29,plain,(
% 7.48/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.48/1.49    inference(nnf_transformation,[],[f1])).
% 7.48/1.49  
% 7.48/1.49  fof(f30,plain,(
% 7.48/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.48/1.49    inference(rectify,[],[f29])).
% 7.48/1.49  
% 7.48/1.49  fof(f31,plain,(
% 7.48/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.48/1.49    introduced(choice_axiom,[])).
% 7.48/1.49  
% 7.48/1.49  fof(f32,plain,(
% 7.48/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.48/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.48/1.49  
% 7.48/1.49  fof(f47,plain,(
% 7.48/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f32])).
% 7.48/1.49  
% 7.48/1.49  fof(f2,axiom,(
% 7.48/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f33,plain,(
% 7.48/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.48/1.49    inference(nnf_transformation,[],[f2])).
% 7.48/1.49  
% 7.48/1.49  fof(f49,plain,(
% 7.48/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f33])).
% 7.48/1.49  
% 7.48/1.49  fof(f50,plain,(
% 7.48/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.48/1.49    inference(cnf_transformation,[],[f33])).
% 7.48/1.49  
% 7.48/1.49  fof(f6,axiom,(
% 7.48/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f17,plain,(
% 7.48/1.49    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.48/1.49    inference(ennf_transformation,[],[f6])).
% 7.48/1.49  
% 7.48/1.49  fof(f36,plain,(
% 7.48/1.49    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.48/1.49    inference(nnf_transformation,[],[f17])).
% 7.48/1.49  
% 7.48/1.49  fof(f57,plain,(
% 7.48/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f36])).
% 7.48/1.49  
% 7.48/1.49  fof(f9,axiom,(
% 7.48/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f21,plain,(
% 7.48/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.48/1.49    inference(ennf_transformation,[],[f9])).
% 7.48/1.49  
% 7.48/1.49  fof(f22,plain,(
% 7.48/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.48/1.49    inference(flattening,[],[f21])).
% 7.48/1.49  
% 7.48/1.49  fof(f61,plain,(
% 7.48/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f22])).
% 7.48/1.49  
% 7.48/1.49  fof(f78,plain,(
% 7.48/1.49    v1_funct_1(sK7)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f73,plain,(
% 7.48/1.49    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f5,axiom,(
% 7.48/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f16,plain,(
% 7.48/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.48/1.49    inference(ennf_transformation,[],[f5])).
% 7.48/1.49  
% 7.48/1.49  fof(f55,plain,(
% 7.48/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.48/1.49    inference(cnf_transformation,[],[f16])).
% 7.48/1.49  
% 7.48/1.49  fof(f81,plain,(
% 7.48/1.49    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f7,axiom,(
% 7.48/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f18,plain,(
% 7.48/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.48/1.49    inference(ennf_transformation,[],[f7])).
% 7.48/1.49  
% 7.48/1.49  fof(f19,plain,(
% 7.48/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.48/1.49    inference(flattening,[],[f18])).
% 7.48/1.49  
% 7.48/1.49  fof(f37,plain,(
% 7.48/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.48/1.49    inference(nnf_transformation,[],[f19])).
% 7.48/1.49  
% 7.48/1.49  fof(f58,plain,(
% 7.48/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f37])).
% 7.48/1.49  
% 7.48/1.49  fof(f74,plain,(
% 7.48/1.49    r1_subset_1(sK4,sK5)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f70,plain,(
% 7.48/1.49    ~v1_xboole_0(sK4)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f72,plain,(
% 7.48/1.49    ~v1_xboole_0(sK5)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f77,plain,(
% 7.48/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f75,plain,(
% 7.48/1.49    v1_funct_1(sK6)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f10,axiom,(
% 7.48/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f23,plain,(
% 7.48/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.48/1.49    inference(ennf_transformation,[],[f10])).
% 7.48/1.49  
% 7.48/1.49  fof(f24,plain,(
% 7.48/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.48/1.49    inference(flattening,[],[f23])).
% 7.48/1.49  
% 7.48/1.49  fof(f38,plain,(
% 7.48/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.48/1.49    inference(nnf_transformation,[],[f24])).
% 7.48/1.49  
% 7.48/1.49  fof(f39,plain,(
% 7.48/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.48/1.49    inference(flattening,[],[f38])).
% 7.48/1.49  
% 7.48/1.49  fof(f62,plain,(
% 7.48/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f39])).
% 7.48/1.49  
% 7.48/1.49  fof(f85,plain,(
% 7.48/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.48/1.49    inference(equality_resolution,[],[f62])).
% 7.48/1.49  
% 7.48/1.49  fof(f11,axiom,(
% 7.48/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.48/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.49  
% 7.48/1.49  fof(f25,plain,(
% 7.48/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.48/1.49    inference(ennf_transformation,[],[f11])).
% 7.48/1.49  
% 7.48/1.49  fof(f26,plain,(
% 7.48/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.48/1.49    inference(flattening,[],[f25])).
% 7.48/1.49  
% 7.48/1.49  fof(f65,plain,(
% 7.48/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f26])).
% 7.48/1.49  
% 7.48/1.49  fof(f66,plain,(
% 7.48/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f26])).
% 7.48/1.49  
% 7.48/1.49  fof(f67,plain,(
% 7.48/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f26])).
% 7.48/1.49  
% 7.48/1.49  fof(f69,plain,(
% 7.48/1.49    ~v1_xboole_0(sK3)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f79,plain,(
% 7.48/1.49    v1_funct_2(sK7,sK5,sK3)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f76,plain,(
% 7.48/1.49    v1_funct_2(sK6,sK4,sK3)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f68,plain,(
% 7.48/1.49    ~v1_xboole_0(sK2)),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f71,plain,(
% 7.48/1.49    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 7.48/1.49    inference(cnf_transformation,[],[f46])).
% 7.48/1.49  
% 7.48/1.49  fof(f63,plain,(
% 7.48/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.48/1.49    inference(cnf_transformation,[],[f39])).
% 7.48/1.49  
% 7.48/1.49  fof(f84,plain,(
% 7.48/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.48/1.49    inference(equality_resolution,[],[f63])).
% 7.48/1.49  
% 7.48/1.49  cnf(c_22,negated_conjecture,
% 7.48/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.48/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1228,negated_conjecture,
% 7.48/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2068,plain,
% 7.48/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1228]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_13,plain,
% 7.48/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.48/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1235,plain,
% 7.48/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.48/1.49      | v1_relat_1(X0_54) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2062,plain,
% 7.48/1.49      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.48/1.49      | v1_relat_1(X0_54) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1235]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3414,plain,
% 7.48/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2068,c_2062]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_4,plain,
% 7.48/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.48/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1242,plain,
% 7.48/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2055,plain,
% 7.48/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6,plain,
% 7.48/1.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.48/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1240,plain,
% 7.48/1.49      ( r1_xboole_0(X0_54,X1_54) | r2_hidden(sK1(X0_54,X1_54),X1_54) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2057,plain,
% 7.48/1.49      ( r1_xboole_0(X0_54,X1_54) = iProver_top
% 7.48/1.49      | r2_hidden(sK1(X0_54,X1_54),X1_54) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1,plain,
% 7.48/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.48/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1245,plain,
% 7.48/1.49      ( ~ r2_hidden(X0_56,X0_54) | ~ v1_xboole_0(X0_54) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2052,plain,
% 7.48/1.49      ( r2_hidden(X0_56,X0_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3354,plain,
% 7.48/1.49      ( r1_xboole_0(X0_54,X1_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) != iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2057,c_2052]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3,plain,
% 7.48/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.48/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1243,plain,
% 7.48/1.49      ( ~ r1_xboole_0(X0_54,X1_54) | k3_xboole_0(X0_54,X1_54) = k1_xboole_0 ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2054,plain,
% 7.48/1.49      ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
% 7.48/1.49      | r1_xboole_0(X0_54,X1_54) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1243]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3663,plain,
% 7.48/1.49      ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
% 7.48/1.49      | v1_xboole_0(X1_54) != iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3354,c_2054]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_5353,plain,
% 7.48/1.49      ( k3_xboole_0(X0_54,k1_xboole_0) = k1_xboole_0 ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2055,c_3663]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2,plain,
% 7.48/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.48/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1244,plain,
% 7.48/1.49      ( r1_xboole_0(X0_54,X1_54) | k3_xboole_0(X0_54,X1_54) != k1_xboole_0 ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2053,plain,
% 7.48/1.49      ( k3_xboole_0(X0_54,X1_54) != k1_xboole_0
% 7.48/1.49      | r1_xboole_0(X0_54,X1_54) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6261,plain,
% 7.48/1.49      ( r1_xboole_0(X0_54,k1_xboole_0) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_5353,c_2053]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_9,plain,
% 7.48/1.49      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.48/1.49      | ~ v1_relat_1(X0)
% 7.48/1.49      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.48/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1237,plain,
% 7.48/1.49      ( ~ r1_xboole_0(k1_relat_1(X0_54),X1_54)
% 7.48/1.49      | ~ v1_relat_1(X0_54)
% 7.48/1.49      | k7_relat_1(X0_54,X1_54) = k1_xboole_0 ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2060,plain,
% 7.48/1.49      ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 7.48/1.49      | r1_xboole_0(k1_relat_1(X0_54),X1_54) != iProver_top
% 7.48/1.49      | v1_relat_1(X0_54) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1237]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6267,plain,
% 7.48/1.49      ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
% 7.48/1.49      | v1_relat_1(X0_54) != iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_6261,c_2060]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_7647,plain,
% 7.48/1.49      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3414,c_6267]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_14,plain,
% 7.48/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.48/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1234,plain,
% 7.48/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.48/1.49      | ~ v1_funct_1(X0_54)
% 7.48/1.49      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2063,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.48/1.49      | v1_funct_1(X2_54) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1234]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3680,plain,
% 7.48/1.49      ( k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54)
% 7.48/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2068,c_2063]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_24,negated_conjecture,
% 7.48/1.49      ( v1_funct_1(sK7) ),
% 7.48/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2507,plain,
% 7.48/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.48/1.49      | ~ v1_funct_1(sK7)
% 7.48/1.49      | k2_partfun1(X0_54,X1_54,sK7,X2_54) = k7_relat_1(sK7,X2_54) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_1234]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2708,plain,
% 7.48/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.48/1.49      | ~ v1_funct_1(sK7)
% 7.48/1.49      | k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_2507]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3955,plain,
% 7.48/1.49      ( k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54) ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_3680,c_24,c_22,c_2708]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_29,negated_conjecture,
% 7.48/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.48/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1222,negated_conjecture,
% 7.48/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_29]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2074,plain,
% 7.48/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1222]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_8,plain,
% 7.48/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.48/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.48/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1238,plain,
% 7.48/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.48/1.49      | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2059,plain,
% 7.48/1.49      ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3337,plain,
% 7.48/1.49      ( k9_subset_1(sK2,X0_54,sK5) = k3_xboole_0(X0_54,sK5) ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2074,c_2059]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_21,negated_conjecture,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.48/1.49      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.48/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1229,negated_conjecture,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.48/1.49      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3512,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.48/1.49      | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
% 7.48/1.49      inference(demodulation,[status(thm)],[c_3337,c_1229]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_12,plain,
% 7.48/1.49      ( ~ r1_subset_1(X0,X1)
% 7.48/1.49      | r1_xboole_0(X0,X1)
% 7.48/1.49      | v1_xboole_0(X0)
% 7.48/1.49      | v1_xboole_0(X1) ),
% 7.48/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_28,negated_conjecture,
% 7.48/1.49      ( r1_subset_1(sK4,sK5) ),
% 7.48/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_487,plain,
% 7.48/1.49      ( r1_xboole_0(X0,X1)
% 7.48/1.49      | v1_xboole_0(X0)
% 7.48/1.49      | v1_xboole_0(X1)
% 7.48/1.49      | sK5 != X1
% 7.48/1.49      | sK4 != X0 ),
% 7.48/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_488,plain,
% 7.48/1.49      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 7.48/1.49      inference(unflattening,[status(thm)],[c_487]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_32,negated_conjecture,
% 7.48/1.49      ( ~ v1_xboole_0(sK4) ),
% 7.48/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_30,negated_conjecture,
% 7.48/1.49      ( ~ v1_xboole_0(sK5) ),
% 7.48/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_490,plain,
% 7.48/1.49      ( r1_xboole_0(sK4,sK5) ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_488,c_32,c_30]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1214,plain,
% 7.48/1.49      ( r1_xboole_0(sK4,sK5) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_490]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2082,plain,
% 7.48/1.49      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1214]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2951,plain,
% 7.48/1.49      ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2082,c_2054]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3513,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.48/1.49      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
% 7.48/1.49      inference(light_normalisation,[status(thm)],[c_3512,c_2951]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3959,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.48/1.49      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.48/1.49      inference(demodulation,[status(thm)],[c_3955,c_3513]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_25,negated_conjecture,
% 7.48/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.48/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1225,negated_conjecture,
% 7.48/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2071,plain,
% 7.48/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1225]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3681,plain,
% 7.48/1.49      ( k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54)
% 7.48/1.49      | v1_funct_1(sK6) != iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2071,c_2063]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_27,negated_conjecture,
% 7.48/1.49      ( v1_funct_1(sK6) ),
% 7.48/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2512,plain,
% 7.48/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.48/1.49      | ~ v1_funct_1(sK6)
% 7.48/1.49      | k2_partfun1(X0_54,X1_54,sK6,X2_54) = k7_relat_1(sK6,X2_54) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_1234]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2713,plain,
% 7.48/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.48/1.49      | ~ v1_funct_1(sK6)
% 7.48/1.49      | k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_2512]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3961,plain,
% 7.48/1.49      ( k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54) ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_3681,c_27,c_25,c_2713]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_4087,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.48/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.48/1.49      inference(demodulation,[status(thm)],[c_3959,c_3961]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_7878,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.48/1.49      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 7.48/1.49      inference(demodulation,[status(thm)],[c_7647,c_4087]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2428,plain,
% 7.48/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.48/1.49      | v1_relat_1(sK6) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_1235]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2643,plain,
% 7.48/1.49      ( r1_xboole_0(X0_54,k1_xboole_0)
% 7.48/1.49      | r2_hidden(sK1(X0_54,k1_xboole_0),k1_xboole_0) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_1240]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2990,plain,
% 7.48/1.49      ( r1_xboole_0(k1_relat_1(sK6),k1_xboole_0)
% 7.48/1.49      | r2_hidden(sK1(k1_relat_1(sK6),k1_xboole_0),k1_xboole_0) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_2643]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2619,plain,
% 7.48/1.49      ( ~ r1_xboole_0(k1_relat_1(sK6),X0_54)
% 7.48/1.49      | ~ v1_relat_1(sK6)
% 7.48/1.49      | k7_relat_1(sK6,X0_54) = k1_xboole_0 ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_1237]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2991,plain,
% 7.48/1.49      ( ~ r1_xboole_0(k1_relat_1(sK6),k1_xboole_0)
% 7.48/1.49      | ~ v1_relat_1(sK6)
% 7.48/1.49      | k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_2619]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2416,plain,
% 7.48/1.49      ( ~ r2_hidden(X0_56,k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_1245]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2642,plain,
% 7.48/1.49      ( ~ r2_hidden(sK1(X0_54,k1_xboole_0),k1_xboole_0)
% 7.48/1.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_2416]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3881,plain,
% 7.48/1.49      ( ~ r2_hidden(sK1(k1_relat_1(sK6),k1_xboole_0),k1_xboole_0)
% 7.48/1.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.48/1.49      inference(instantiation,[status(thm)],[c_2642]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_17,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_1(X3)
% 7.48/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X1)
% 7.48/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.48/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_20,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_1(X3)
% 7.48/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X1) ),
% 7.48/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_19,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_1(X3)
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X1) ),
% 7.48/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_18,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_1(X3)
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X1) ),
% 7.48/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_188,plain,
% 7.48/1.49      ( ~ v1_funct_1(X3)
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X1)
% 7.48/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_17,c_20,c_19,c_18]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_189,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_1(X3)
% 7.48/1.49      | v1_xboole_0(X1)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_188]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1216,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.48/1.49      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.48/1.49      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.48/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.48/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.48/1.49      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.48/1.49      | ~ v1_funct_1(X0_54)
% 7.48/1.49      | ~ v1_funct_1(X3_54)
% 7.48/1.49      | v1_xboole_0(X1_54)
% 7.48/1.49      | v1_xboole_0(X2_54)
% 7.48/1.49      | v1_xboole_0(X4_54)
% 7.48/1.49      | v1_xboole_0(X5_54)
% 7.48/1.49      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_189]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2080,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 7.48/1.49      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.48/1.49      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.48/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.48/1.49      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.48/1.49      | v1_funct_1(X2_54) != iProver_top
% 7.48/1.49      | v1_funct_1(X5_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X3_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X4_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_5865,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | v1_funct_1(sK7) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3955,c_2080]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_33,negated_conjecture,
% 7.48/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.48/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_36,plain,
% 7.48/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_39,plain,
% 7.48/1.49      ( v1_xboole_0(sK5) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_45,plain,
% 7.48/1.49      ( v1_funct_1(sK7) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_23,negated_conjecture,
% 7.48/1.49      ( v1_funct_2(sK7,sK5,sK3) ),
% 7.48/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_46,plain,
% 7.48/1.49      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_47,plain,
% 7.48/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6365,plain,
% 7.48/1.49      ( v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
% 7.48/1.49      | k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_5865,c_36,c_39,c_45,c_46,c_47]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6366,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_6365]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6381,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.48/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(sK6) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3961,c_6366]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_37,plain,
% 7.48/1.49      ( v1_xboole_0(sK4) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_42,plain,
% 7.48/1.49      ( v1_funct_1(sK6) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_26,negated_conjecture,
% 7.48/1.49      ( v1_funct_2(sK6,sK4,sK3) ),
% 7.48/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_43,plain,
% 7.48/1.49      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_44,plain,
% 7.48/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6473,plain,
% 7.48/1.49      ( v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_6381,c_37,c_42,c_43,c_44]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6474,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_6473]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6484,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3337,c_6474]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6485,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(light_normalisation,[status(thm)],[c_6484,c_2951]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6486,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(demodulation,[status(thm)],[c_6485,c_3337]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6487,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(light_normalisation,[status(thm)],[c_6486,c_2951]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_34,negated_conjecture,
% 7.48/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.48/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_31,negated_conjecture,
% 7.48/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 7.48/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_6488,plain,
% 7.48/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 7.48/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 7.48/1.49      | v1_xboole_0(sK2)
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.48/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_6487]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_18128,plain,
% 7.48/1.49      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_6487,c_34,c_31,c_29,c_6488]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_18129,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_18128]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_3415,plain,
% 7.48/1.49      ( v1_relat_1(sK6) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2071,c_2062]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_7648,plain,
% 7.48/1.49      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3415,c_6267]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_18130,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.48/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.48/1.49      inference(light_normalisation,[status(thm)],[c_18129,c_7647,c_7648]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_18131,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
% 7.48/1.49      inference(equality_resolution_simp,[status(thm)],[c_18130]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_19281,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_7878,c_25,c_4,c_2428,c_2990,c_2991,c_3881,c_18131]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1232,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.48/1.49      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.48/1.49      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.48/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.48/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.48/1.49      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.48/1.49      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
% 7.48/1.49      | ~ v1_funct_1(X0_54)
% 7.48/1.49      | ~ v1_funct_1(X3_54)
% 7.48/1.49      | v1_xboole_0(X1_54)
% 7.48/1.49      | v1_xboole_0(X2_54)
% 7.48/1.49      | v1_xboole_0(X4_54)
% 7.48/1.49      | v1_xboole_0(X5_54) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2065,plain,
% 7.48/1.49      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.48/1.49      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.48/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.48/1.49      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.48/1.49      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
% 7.48/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.48/1.49      | v1_funct_1(X3_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X5_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X4_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_5135,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.48/1.49      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.48/1.49      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.48/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.48/1.49      | v1_funct_1(X5_54) != iProver_top
% 7.48/1.49      | v1_funct_1(X4_54) != iProver_top
% 7.48/1.49      | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X3_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2065,c_2063]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1230,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.48/1.49      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.48/1.49      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.48/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.48/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.48/1.49      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.48/1.49      | ~ v1_funct_1(X0_54)
% 7.48/1.49      | ~ v1_funct_1(X3_54)
% 7.48/1.49      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
% 7.48/1.49      | v1_xboole_0(X1_54)
% 7.48/1.49      | v1_xboole_0(X2_54)
% 7.48/1.49      | v1_xboole_0(X4_54)
% 7.48/1.49      | v1_xboole_0(X5_54) ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2067,plain,
% 7.48/1.49      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.48/1.49      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.48/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.48/1.49      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.48/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.48/1.49      | v1_funct_1(X3_54) != iProver_top
% 7.48/1.49      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
% 7.48/1.49      | v1_xboole_0(X5_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X4_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_11677,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.48/1.49      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.48/1.49      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.48/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.48/1.49      | v1_funct_1(X5_54) != iProver_top
% 7.48/1.49      | v1_funct_1(X4_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X3_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_5135,c_2067]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_11681,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
% 7.48/1.49      | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
% 7.48/1.49      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(X2_54) != iProver_top
% 7.48/1.49      | v1_funct_1(sK7) != iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2068,c_11677]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_12046,plain,
% 7.48/1.49      ( v1_funct_1(X2_54) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
% 7.48/1.49      | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_11681,c_36,c_39,c_45,c_46]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_12047,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
% 7.48/1.49      | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(X2_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_12046]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_12061,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
% 7.48/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(sK6) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2071,c_12047]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_12445,plain,
% 7.48/1.49      ( v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_12061,c_37,c_42,c_43]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_12446,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_12445]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_12455,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54)
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_2074,c_12446]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_35,plain,
% 7.48/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_38,plain,
% 7.48/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_12506,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_12455,c_35,c_38]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_16,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_1(X3)
% 7.48/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X1)
% 7.48/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.48/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_195,plain,
% 7.48/1.49      ( ~ v1_funct_1(X3)
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X1)
% 7.48/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_16,c_20,c_19,c_18]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_196,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.48/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.48/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.48/1.49      | ~ v1_funct_1(X0)
% 7.48/1.49      | ~ v1_funct_1(X3)
% 7.48/1.49      | v1_xboole_0(X1)
% 7.48/1.49      | v1_xboole_0(X2)
% 7.48/1.49      | v1_xboole_0(X4)
% 7.48/1.49      | v1_xboole_0(X5)
% 7.48/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_195]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_1215,plain,
% 7.48/1.49      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.48/1.49      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.48/1.49      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.48/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.48/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.48/1.49      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.48/1.49      | ~ v1_funct_1(X0_54)
% 7.48/1.49      | ~ v1_funct_1(X3_54)
% 7.48/1.49      | v1_xboole_0(X1_54)
% 7.48/1.49      | v1_xboole_0(X2_54)
% 7.48/1.49      | v1_xboole_0(X4_54)
% 7.48/1.49      | v1_xboole_0(X5_54)
% 7.48/1.49      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 7.48/1.49      inference(subtyping,[status(esa)],[c_196]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_2081,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 7.48/1.49      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.48/1.49      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.48/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.48/1.49      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.48/1.49      | v1_funct_1(X2_54) != iProver_top
% 7.48/1.49      | v1_funct_1(X5_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X3_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X4_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_1215]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_7100,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | v1_funct_1(sK7) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3955,c_2081]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_14733,plain,
% 7.48/1.49      ( v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.48/1.49      | k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_7100,c_36,c_39,c_45,c_46,c_47]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_14734,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.48/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_14733]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_14754,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,X0_54,sK5))
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3337,c_14734]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_14764,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(light_normalisation,[status(thm)],[c_14754,c_3337]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_40,plain,
% 7.48/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.48/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15147,plain,
% 7.48/1.49      ( v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_14764,c_35,c_40]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15148,plain,
% 7.48/1.49      ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
% 7.48/1.49      | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.48/1.49      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_15147]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15161,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.48/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_funct_1(sK6) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3961,c_15148]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15246,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k1_xboole_0 != k1_xboole_0
% 7.48/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_funct_1(sK6) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.48/1.49      inference(light_normalisation,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_15161,c_2951,c_7647,c_7648]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15247,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_funct_1(sK6) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.48/1.49      inference(equality_resolution_simp,[status(thm)],[c_15246]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15248,plain,
% 7.48/1.49      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_funct_1(sK6) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.48/1.49      inference(demodulation,[status(thm)],[c_15247,c_12506]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_14749,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.48/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.48/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | v1_funct_1(sK6) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3961,c_14734]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15083,plain,
% 7.48/1.49      ( v1_xboole_0(X0_54) = iProver_top
% 7.48/1.49      | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_14749,c_37,c_42,c_43,c_44]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15084,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.48/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.48/1.49      inference(renaming,[status(thm)],[c_15083]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15094,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(superposition,[status(thm)],[c_3337,c_15084]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15095,plain,
% 7.48/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(light_normalisation,[status(thm)],[c_15094,c_2951,c_7647]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15096,plain,
% 7.48/1.49      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k1_xboole_0
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(demodulation,[status(thm)],[c_15095,c_3337,c_12506]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15097,plain,
% 7.48/1.49      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | k1_xboole_0 != k1_xboole_0
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(light_normalisation,[status(thm)],[c_15096,c_2951,c_7648]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15098,plain,
% 7.48/1.49      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.48/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.48/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.48/1.49      inference(equality_resolution_simp,[status(thm)],[c_15097]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_15264,plain,
% 7.48/1.49      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
% 7.48/1.49      inference(global_propositional_subsumption,
% 7.48/1.49                [status(thm)],
% 7.48/1.49                [c_15248,c_35,c_38,c_40,c_15098]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_19283,plain,
% 7.48/1.49      ( sK7 != sK7 ),
% 7.48/1.49      inference(demodulation,[status(thm)],[c_19281,c_12506,c_15264]) ).
% 7.48/1.49  
% 7.48/1.49  cnf(c_19284,plain,
% 7.48/1.49      ( $false ),
% 7.48/1.49      inference(equality_resolution_simp,[status(thm)],[c_19283]) ).
% 7.48/1.49  
% 7.48/1.49  
% 7.48/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.48/1.49  
% 7.48/1.49  ------                               Statistics
% 7.48/1.49  
% 7.48/1.49  ------ General
% 7.48/1.49  
% 7.48/1.49  abstr_ref_over_cycles:                  0
% 7.48/1.49  abstr_ref_under_cycles:                 0
% 7.48/1.49  gc_basic_clause_elim:                   0
% 7.48/1.49  forced_gc_time:                         0
% 7.48/1.49  parsing_time:                           0.013
% 7.48/1.49  unif_index_cands_time:                  0.
% 7.48/1.49  unif_index_add_time:                    0.
% 7.48/1.49  orderings_time:                         0.
% 7.48/1.49  out_proof_time:                         0.019
% 7.48/1.49  total_time:                             0.949
% 7.48/1.49  num_of_symbols:                         60
% 7.48/1.49  num_of_terms:                           33800
% 7.48/1.49  
% 7.48/1.49  ------ Preprocessing
% 7.48/1.49  
% 7.48/1.49  num_of_splits:                          0
% 7.48/1.49  num_of_split_atoms:                     0
% 7.48/1.49  num_of_reused_defs:                     0
% 7.48/1.49  num_eq_ax_congr_red:                    31
% 7.48/1.49  num_of_sem_filtered_clauses:            1
% 7.48/1.49  num_of_subtypes:                        3
% 7.48/1.49  monotx_restored_types:                  0
% 7.48/1.49  sat_num_of_epr_types:                   0
% 7.48/1.49  sat_num_of_non_cyclic_types:            0
% 7.48/1.49  sat_guarded_non_collapsed_types:        1
% 7.48/1.49  num_pure_diseq_elim:                    0
% 7.48/1.49  simp_replaced_by:                       0
% 7.48/1.49  res_preprocessed:                       167
% 7.48/1.49  prep_upred:                             0
% 7.48/1.49  prep_unflattend:                        32
% 7.48/1.49  smt_new_axioms:                         0
% 7.48/1.49  pred_elim_cands:                        7
% 7.48/1.49  pred_elim:                              1
% 7.48/1.49  pred_elim_cl:                           2
% 7.48/1.49  pred_elim_cycles:                       5
% 7.48/1.49  merged_defs:                            8
% 7.48/1.49  merged_defs_ncl:                        0
% 7.48/1.49  bin_hyper_res:                          8
% 7.48/1.49  prep_cycles:                            4
% 7.48/1.49  pred_elim_time:                         0.008
% 7.48/1.49  splitting_time:                         0.
% 7.48/1.49  sem_filter_time:                        0.
% 7.48/1.49  monotx_time:                            0.
% 7.48/1.49  subtype_inf_time:                       0.001
% 7.48/1.49  
% 7.48/1.49  ------ Problem properties
% 7.48/1.49  
% 7.48/1.49  clauses:                                33
% 7.48/1.49  conjectures:                            13
% 7.48/1.49  epr:                                    12
% 7.48/1.49  horn:                                   24
% 7.48/1.49  ground:                                 15
% 7.48/1.49  unary:                                  14
% 7.48/1.49  binary:                                 8
% 7.48/1.49  lits:                                   129
% 7.48/1.49  lits_eq:                                15
% 7.48/1.49  fd_pure:                                0
% 7.48/1.49  fd_pseudo:                              0
% 7.48/1.49  fd_cond:                                0
% 7.48/1.49  fd_pseudo_cond:                         0
% 7.48/1.49  ac_symbols:                             0
% 7.48/1.49  
% 7.48/1.49  ------ Propositional Solver
% 7.48/1.49  
% 7.48/1.49  prop_solver_calls:                      28
% 7.48/1.49  prop_fast_solver_calls:                 3674
% 7.48/1.49  smt_solver_calls:                       0
% 7.48/1.49  smt_fast_solver_calls:                  0
% 7.48/1.49  prop_num_of_clauses:                    7210
% 7.48/1.49  prop_preprocess_simplified:             13484
% 7.48/1.49  prop_fo_subsumed:                       289
% 7.48/1.49  prop_solver_time:                       0.
% 7.48/1.49  smt_solver_time:                        0.
% 7.48/1.49  smt_fast_solver_time:                   0.
% 7.48/1.49  prop_fast_solver_time:                  0.
% 7.48/1.49  prop_unsat_core_time:                   0.
% 7.48/1.49  
% 7.48/1.49  ------ QBF
% 7.48/1.49  
% 7.48/1.49  qbf_q_res:                              0
% 7.48/1.49  qbf_num_tautologies:                    0
% 7.48/1.49  qbf_prep_cycles:                        0
% 7.48/1.49  
% 7.48/1.49  ------ BMC1
% 7.48/1.49  
% 7.48/1.49  bmc1_current_bound:                     -1
% 7.48/1.49  bmc1_last_solved_bound:                 -1
% 7.48/1.49  bmc1_unsat_core_size:                   -1
% 7.48/1.49  bmc1_unsat_core_parents_size:           -1
% 7.48/1.49  bmc1_merge_next_fun:                    0
% 7.48/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.48/1.49  
% 7.48/1.49  ------ Instantiation
% 7.48/1.49  
% 7.48/1.49  inst_num_of_clauses:                    1576
% 7.48/1.49  inst_num_in_passive:                    56
% 7.48/1.49  inst_num_in_active:                     847
% 7.48/1.49  inst_num_in_unprocessed:                673
% 7.48/1.49  inst_num_of_loops:                      950
% 7.48/1.49  inst_num_of_learning_restarts:          0
% 7.48/1.49  inst_num_moves_active_passive:          100
% 7.48/1.49  inst_lit_activity:                      0
% 7.48/1.49  inst_lit_activity_moves:                1
% 7.48/1.49  inst_num_tautologies:                   0
% 7.48/1.49  inst_num_prop_implied:                  0
% 7.48/1.49  inst_num_existing_simplified:           0
% 7.48/1.49  inst_num_eq_res_simplified:             0
% 7.48/1.49  inst_num_child_elim:                    0
% 7.48/1.49  inst_num_of_dismatching_blockings:      193
% 7.48/1.49  inst_num_of_non_proper_insts:           1159
% 7.48/1.49  inst_num_of_duplicates:                 0
% 7.48/1.49  inst_inst_num_from_inst_to_res:         0
% 7.48/1.49  inst_dismatching_checking_time:         0.
% 7.48/1.49  
% 7.48/1.49  ------ Resolution
% 7.48/1.49  
% 7.48/1.49  res_num_of_clauses:                     0
% 7.48/1.49  res_num_in_passive:                     0
% 7.48/1.49  res_num_in_active:                      0
% 7.48/1.49  res_num_of_loops:                       171
% 7.48/1.49  res_forward_subset_subsumed:            35
% 7.48/1.49  res_backward_subset_subsumed:           0
% 7.48/1.49  res_forward_subsumed:                   0
% 7.48/1.49  res_backward_subsumed:                  0
% 7.48/1.49  res_forward_subsumption_resolution:     0
% 7.48/1.49  res_backward_subsumption_resolution:    0
% 7.48/1.49  res_clause_to_clause_subsumption:       2313
% 7.48/1.49  res_orphan_elimination:                 0
% 7.48/1.49  res_tautology_del:                      44
% 7.48/1.49  res_num_eq_res_simplified:              0
% 7.48/1.49  res_num_sel_changes:                    0
% 7.48/1.49  res_moves_from_active_to_pass:          0
% 7.48/1.49  
% 7.48/1.49  ------ Superposition
% 7.48/1.49  
% 7.48/1.49  sup_time_total:                         0.
% 7.48/1.49  sup_time_generating:                    0.
% 7.48/1.49  sup_time_sim_full:                      0.
% 7.48/1.49  sup_time_sim_immed:                     0.
% 7.48/1.49  
% 7.48/1.49  sup_num_of_clauses:                     314
% 7.48/1.49  sup_num_in_active:                      185
% 7.48/1.49  sup_num_in_passive:                     129
% 7.48/1.49  sup_num_of_loops:                       188
% 7.48/1.49  sup_fw_superposition:                   274
% 7.48/1.49  sup_bw_superposition:                   111
% 7.48/1.49  sup_immediate_simplified:               182
% 7.48/1.49  sup_given_eliminated:                   0
% 7.48/1.49  comparisons_done:                       0
% 7.48/1.49  comparisons_avoided:                    0
% 7.48/1.49  
% 7.48/1.49  ------ Simplifications
% 7.48/1.49  
% 7.48/1.49  
% 7.48/1.49  sim_fw_subset_subsumed:                 29
% 7.48/1.49  sim_bw_subset_subsumed:                 3
% 7.48/1.49  sim_fw_subsumed:                        19
% 7.48/1.49  sim_bw_subsumed:                        8
% 7.48/1.49  sim_fw_subsumption_res:                 7
% 7.48/1.49  sim_bw_subsumption_res:                 0
% 7.48/1.49  sim_tautology_del:                      1
% 7.48/1.49  sim_eq_tautology_del:                   9
% 7.48/1.49  sim_eq_res_simp:                        9
% 7.48/1.49  sim_fw_demodulated:                     76
% 7.48/1.49  sim_bw_demodulated:                     4
% 7.48/1.49  sim_light_normalised:                   83
% 7.48/1.49  sim_joinable_taut:                      0
% 7.48/1.49  sim_joinable_simp:                      0
% 7.48/1.49  sim_ac_normalised:                      0
% 7.48/1.49  sim_smt_subsumption:                    0
% 7.48/1.49  
%------------------------------------------------------------------------------
