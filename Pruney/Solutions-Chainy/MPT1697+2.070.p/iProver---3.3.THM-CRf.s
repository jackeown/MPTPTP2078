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

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  217 (1660 expanded)
%              Number of clauses        :  123 ( 418 expanded)
%              Number of leaves         :   24 ( 634 expanded)
%              Depth                    :   25
%              Number of atoms          : 1125 (20556 expanded)
%              Number of equality atoms :  395 (4840 expanded)
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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f36,f56,f55,f54,f53,f52,f51])).

fof(f98,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
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
    inference(rectify,[],[f4])).

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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f42])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f99,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f81])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2142,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4175,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_2148])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2152,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_544,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_17])).

cnf(c_2127,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_8414,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_2127])).

cnf(c_8419,plain,
    ( k7_relat_1(sK7,k1_relat_1(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_4175,c_8414])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2157,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2155,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2160,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3584,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_2160])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2158,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6500,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3584,c_2158])).

cnf(c_6964,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2157,c_6500])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2159,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7276,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6964,c_2159])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2149,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7283,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7276,c_2149])).

cnf(c_8057,plain,
    ( k7_relat_1(k7_relat_1(sK7,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4175,c_7283])).

cnf(c_8487,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8419,c_8057])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2136,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2150,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3316,plain,
    ( r1_tarski(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_2150])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_319,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_402,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_319])).

cnf(c_2128,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_3974,plain,
    ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_3316,c_2128])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2139,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2147,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4579,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_2147])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_49,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6207,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4579,c_49])).

cnf(c_4578,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_2147])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_52,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6186,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4578,c_52])).

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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f105])).

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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_228,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_27,c_26,c_25])).

cnf(c_229,plain,
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
    inference(renaming,[status(thm)],[c_228])).

cnf(c_2130,plain,
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
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_6190,plain,
    ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6186,c_2130])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_43,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_46,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_53,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_54,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6343,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
    | k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6190,c_43,c_46,c_52,c_53,c_54])).

cnf(c_6344,plain,
    ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6343])).

cnf(c_6350,plain,
    ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6207,c_6344])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_44,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_50,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_51,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6574,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6350,c_44,c_49,c_50,c_51])).

cnf(c_6575,plain,
    ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6574])).

cnf(c_6581,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3974,c_6575])).

cnf(c_19,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_35,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_599,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_600,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_602,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_39,c_37])).

cnf(c_2126,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_3139,plain,
    ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2126,c_2158])).

cnf(c_6582,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6581,c_3139])).

cnf(c_6583,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6582,c_3974])).

cnf(c_6584,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6583,c_3139])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_28,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4061,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_3974,c_28])).

cnf(c_4062,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4061,c_3139])).

cnf(c_6189,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6186,c_4062])).

cnf(c_6279,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6189,c_6207])).

cnf(c_6588,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6584])).

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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_235,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_27,c_26,c_25])).

cnf(c_236,plain,
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
    inference(renaming,[status(thm)],[c_235])).

cnf(c_2129,plain,
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
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_6191,plain,
    ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6186,c_2129])).

cnf(c_6631,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6191,c_43,c_46,c_52,c_53,c_54])).

cnf(c_6632,plain,
    ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6631])).

cnf(c_6638,plain,
    ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6207,c_6632])).

cnf(c_6653,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6638,c_44,c_49,c_50,c_51])).

cnf(c_6654,plain,
    ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6653])).

cnf(c_6660,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3974,c_6654])).

cnf(c_6661,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6660,c_3139])).

cnf(c_6662,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6661,c_3974])).

cnf(c_6663,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6662,c_3139])).

cnf(c_6667,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6663])).

cnf(c_7574,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6584,c_41,c_38,c_36,c_6279,c_6588,c_6667])).

cnf(c_8840,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8487,c_7574])).

cnf(c_4176,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_2148])).

cnf(c_8420,plain,
    ( k7_relat_1(sK6,k1_relat_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_4176,c_8414])).

cnf(c_8058,plain,
    ( k7_relat_1(k7_relat_1(sK6,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4176,c_7283])).

cnf(c_8836,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8420,c_8058])).

cnf(c_8841,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8840,c_8836])).

cnf(c_8842,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8841])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.72/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.99  
% 3.72/0.99  ------  iProver source info
% 3.72/0.99  
% 3.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.99  git: non_committed_changes: false
% 3.72/0.99  git: last_make_outside_of_git: false
% 3.72/0.99  
% 3.72/0.99  ------ 
% 3.72/0.99  
% 3.72/0.99  ------ Input Options
% 3.72/0.99  
% 3.72/0.99  --out_options                           all
% 3.72/0.99  --tptp_safe_out                         true
% 3.72/0.99  --problem_path                          ""
% 3.72/0.99  --include_path                          ""
% 3.72/0.99  --clausifier                            res/vclausify_rel
% 3.72/0.99  --clausifier_options                    ""
% 3.72/0.99  --stdin                                 false
% 3.72/0.99  --stats_out                             all
% 3.72/0.99  
% 3.72/0.99  ------ General Options
% 3.72/0.99  
% 3.72/0.99  --fof                                   false
% 3.72/0.99  --time_out_real                         305.
% 3.72/0.99  --time_out_virtual                      -1.
% 3.72/0.99  --symbol_type_check                     false
% 3.72/0.99  --clausify_out                          false
% 3.72/0.99  --sig_cnt_out                           false
% 3.72/0.99  --trig_cnt_out                          false
% 3.72/0.99  --trig_cnt_out_tolerance                1.
% 3.72/0.99  --trig_cnt_out_sk_spl                   false
% 3.72/0.99  --abstr_cl_out                          false
% 3.72/0.99  
% 3.72/0.99  ------ Global Options
% 3.72/0.99  
% 3.72/0.99  --schedule                              default
% 3.72/0.99  --add_important_lit                     false
% 3.72/0.99  --prop_solver_per_cl                    1000
% 3.72/0.99  --min_unsat_core                        false
% 3.72/0.99  --soft_assumptions                      false
% 3.72/0.99  --soft_lemma_size                       3
% 3.72/0.99  --prop_impl_unit_size                   0
% 3.72/0.99  --prop_impl_unit                        []
% 3.72/0.99  --share_sel_clauses                     true
% 3.72/0.99  --reset_solvers                         false
% 3.72/0.99  --bc_imp_inh                            [conj_cone]
% 3.72/0.99  --conj_cone_tolerance                   3.
% 3.72/0.99  --extra_neg_conj                        none
% 3.72/0.99  --large_theory_mode                     true
% 3.72/0.99  --prolific_symb_bound                   200
% 3.72/0.99  --lt_threshold                          2000
% 3.72/0.99  --clause_weak_htbl                      true
% 3.72/0.99  --gc_record_bc_elim                     false
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing Options
% 3.72/0.99  
% 3.72/0.99  --preprocessing_flag                    true
% 3.72/0.99  --time_out_prep_mult                    0.1
% 3.72/0.99  --splitting_mode                        input
% 3.72/0.99  --splitting_grd                         true
% 3.72/0.99  --splitting_cvd                         false
% 3.72/0.99  --splitting_cvd_svl                     false
% 3.72/0.99  --splitting_nvd                         32
% 3.72/0.99  --sub_typing                            true
% 3.72/0.99  --prep_gs_sim                           true
% 3.72/0.99  --prep_unflatten                        true
% 3.72/0.99  --prep_res_sim                          true
% 3.72/0.99  --prep_upred                            true
% 3.72/0.99  --prep_sem_filter                       exhaustive
% 3.72/0.99  --prep_sem_filter_out                   false
% 3.72/0.99  --pred_elim                             true
% 3.72/0.99  --res_sim_input                         true
% 3.72/0.99  --eq_ax_congr_red                       true
% 3.72/0.99  --pure_diseq_elim                       true
% 3.72/0.99  --brand_transform                       false
% 3.72/0.99  --non_eq_to_eq                          false
% 3.72/0.99  --prep_def_merge                        true
% 3.72/0.99  --prep_def_merge_prop_impl              false
% 3.72/0.99  --prep_def_merge_mbd                    true
% 3.72/0.99  --prep_def_merge_tr_red                 false
% 3.72/0.99  --prep_def_merge_tr_cl                  false
% 3.72/0.99  --smt_preprocessing                     true
% 3.72/0.99  --smt_ac_axioms                         fast
% 3.72/0.99  --preprocessed_out                      false
% 3.72/0.99  --preprocessed_stats                    false
% 3.72/0.99  
% 3.72/0.99  ------ Abstraction refinement Options
% 3.72/0.99  
% 3.72/0.99  --abstr_ref                             []
% 3.72/0.99  --abstr_ref_prep                        false
% 3.72/0.99  --abstr_ref_until_sat                   false
% 3.72/0.99  --abstr_ref_sig_restrict                funpre
% 3.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.99  --abstr_ref_under                       []
% 3.72/0.99  
% 3.72/0.99  ------ SAT Options
% 3.72/0.99  
% 3.72/0.99  --sat_mode                              false
% 3.72/0.99  --sat_fm_restart_options                ""
% 3.72/0.99  --sat_gr_def                            false
% 3.72/0.99  --sat_epr_types                         true
% 3.72/0.99  --sat_non_cyclic_types                  false
% 3.72/0.99  --sat_finite_models                     false
% 3.72/0.99  --sat_fm_lemmas                         false
% 3.72/0.99  --sat_fm_prep                           false
% 3.72/0.99  --sat_fm_uc_incr                        true
% 3.72/0.99  --sat_out_model                         small
% 3.72/0.99  --sat_out_clauses                       false
% 3.72/0.99  
% 3.72/0.99  ------ QBF Options
% 3.72/0.99  
% 3.72/0.99  --qbf_mode                              false
% 3.72/0.99  --qbf_elim_univ                         false
% 3.72/0.99  --qbf_dom_inst                          none
% 3.72/0.99  --qbf_dom_pre_inst                      false
% 3.72/0.99  --qbf_sk_in                             false
% 3.72/0.99  --qbf_pred_elim                         true
% 3.72/0.99  --qbf_split                             512
% 3.72/0.99  
% 3.72/0.99  ------ BMC1 Options
% 3.72/0.99  
% 3.72/0.99  --bmc1_incremental                      false
% 3.72/0.99  --bmc1_axioms                           reachable_all
% 3.72/0.99  --bmc1_min_bound                        0
% 3.72/0.99  --bmc1_max_bound                        -1
% 3.72/0.99  --bmc1_max_bound_default                -1
% 3.72/0.99  --bmc1_symbol_reachability              true
% 3.72/0.99  --bmc1_property_lemmas                  false
% 3.72/0.99  --bmc1_k_induction                      false
% 3.72/0.99  --bmc1_non_equiv_states                 false
% 3.72/0.99  --bmc1_deadlock                         false
% 3.72/0.99  --bmc1_ucm                              false
% 3.72/0.99  --bmc1_add_unsat_core                   none
% 3.72/0.99  --bmc1_unsat_core_children              false
% 3.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.99  --bmc1_out_stat                         full
% 3.72/0.99  --bmc1_ground_init                      false
% 3.72/0.99  --bmc1_pre_inst_next_state              false
% 3.72/0.99  --bmc1_pre_inst_state                   false
% 3.72/0.99  --bmc1_pre_inst_reach_state             false
% 3.72/0.99  --bmc1_out_unsat_core                   false
% 3.72/0.99  --bmc1_aig_witness_out                  false
% 3.72/0.99  --bmc1_verbose                          false
% 3.72/0.99  --bmc1_dump_clauses_tptp                false
% 3.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.99  --bmc1_dump_file                        -
% 3.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.99  --bmc1_ucm_extend_mode                  1
% 3.72/0.99  --bmc1_ucm_init_mode                    2
% 3.72/0.99  --bmc1_ucm_cone_mode                    none
% 3.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.99  --bmc1_ucm_relax_model                  4
% 3.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.99  --bmc1_ucm_layered_model                none
% 3.72/0.99  --bmc1_ucm_max_lemma_size               10
% 3.72/0.99  
% 3.72/0.99  ------ AIG Options
% 3.72/0.99  
% 3.72/0.99  --aig_mode                              false
% 3.72/0.99  
% 3.72/0.99  ------ Instantiation Options
% 3.72/0.99  
% 3.72/0.99  --instantiation_flag                    true
% 3.72/0.99  --inst_sos_flag                         true
% 3.72/0.99  --inst_sos_phase                        true
% 3.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.99  --inst_lit_sel_side                     num_symb
% 3.72/0.99  --inst_solver_per_active                1400
% 3.72/0.99  --inst_solver_calls_frac                1.
% 3.72/0.99  --inst_passive_queue_type               priority_queues
% 3.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.99  --inst_passive_queues_freq              [25;2]
% 3.72/0.99  --inst_dismatching                      true
% 3.72/0.99  --inst_eager_unprocessed_to_passive     true
% 3.72/0.99  --inst_prop_sim_given                   true
% 3.72/0.99  --inst_prop_sim_new                     false
% 3.72/0.99  --inst_subs_new                         false
% 3.72/0.99  --inst_eq_res_simp                      false
% 3.72/0.99  --inst_subs_given                       false
% 3.72/0.99  --inst_orphan_elimination               true
% 3.72/0.99  --inst_learning_loop_flag               true
% 3.72/0.99  --inst_learning_start                   3000
% 3.72/0.99  --inst_learning_factor                  2
% 3.72/0.99  --inst_start_prop_sim_after_learn       3
% 3.72/0.99  --inst_sel_renew                        solver
% 3.72/0.99  --inst_lit_activity_flag                true
% 3.72/0.99  --inst_restr_to_given                   false
% 3.72/0.99  --inst_activity_threshold               500
% 3.72/0.99  --inst_out_proof                        true
% 3.72/0.99  
% 3.72/0.99  ------ Resolution Options
% 3.72/0.99  
% 3.72/0.99  --resolution_flag                       true
% 3.72/0.99  --res_lit_sel                           adaptive
% 3.72/0.99  --res_lit_sel_side                      none
% 3.72/0.99  --res_ordering                          kbo
% 3.72/0.99  --res_to_prop_solver                    active
% 3.72/0.99  --res_prop_simpl_new                    false
% 3.72/0.99  --res_prop_simpl_given                  true
% 3.72/0.99  --res_passive_queue_type                priority_queues
% 3.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.99  --res_passive_queues_freq               [15;5]
% 3.72/0.99  --res_forward_subs                      full
% 3.72/0.99  --res_backward_subs                     full
% 3.72/0.99  --res_forward_subs_resolution           true
% 3.72/0.99  --res_backward_subs_resolution          true
% 3.72/0.99  --res_orphan_elimination                true
% 3.72/0.99  --res_time_limit                        2.
% 3.72/0.99  --res_out_proof                         true
% 3.72/0.99  
% 3.72/0.99  ------ Superposition Options
% 3.72/0.99  
% 3.72/0.99  --superposition_flag                    true
% 3.72/0.99  --sup_passive_queue_type                priority_queues
% 3.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.99  --demod_completeness_check              fast
% 3.72/0.99  --demod_use_ground                      true
% 3.72/0.99  --sup_to_prop_solver                    passive
% 3.72/0.99  --sup_prop_simpl_new                    true
% 3.72/0.99  --sup_prop_simpl_given                  true
% 3.72/0.99  --sup_fun_splitting                     true
% 3.72/0.99  --sup_smt_interval                      50000
% 3.72/0.99  
% 3.72/0.99  ------ Superposition Simplification Setup
% 3.72/0.99  
% 3.72/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.72/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.72/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.72/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.72/0.99  --sup_immed_triv                        [TrivRules]
% 3.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_immed_bw_main                     []
% 3.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_input_bw                          []
% 3.72/0.99  
% 3.72/0.99  ------ Combination Options
% 3.72/0.99  
% 3.72/0.99  --comb_res_mult                         3
% 3.72/0.99  --comb_sup_mult                         2
% 3.72/0.99  --comb_inst_mult                        10
% 3.72/0.99  
% 3.72/0.99  ------ Debug Options
% 3.72/0.99  
% 3.72/0.99  --dbg_backtrace                         false
% 3.72/0.99  --dbg_dump_prop_clauses                 false
% 3.72/0.99  --dbg_dump_prop_clauses_file            -
% 3.72/0.99  --dbg_out_stat                          false
% 3.72/0.99  ------ Parsing...
% 3.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  ------ Proving...
% 3.72/0.99  ------ Problem Properties 
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  clauses                                 37
% 3.72/0.99  conjectures                             13
% 3.72/0.99  EPR                                     14
% 3.72/0.99  Horn                                    28
% 3.72/0.99  unary                                   15
% 3.72/0.99  binary                                  10
% 3.72/0.99  lits                                    137
% 3.72/0.99  lits eq                                 16
% 3.72/0.99  fd_pure                                 0
% 3.72/0.99  fd_pseudo                               0
% 3.72/0.99  fd_cond                                 0
% 3.72/0.99  fd_pseudo_cond                          1
% 3.72/0.99  AC symbols                              0
% 3.72/0.99  
% 3.72/0.99  ------ Schedule dynamic 5 is on 
% 3.72/0.99  
% 3.72/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ 
% 3.72/0.99  Current options:
% 3.72/0.99  ------ 
% 3.72/0.99  
% 3.72/0.99  ------ Input Options
% 3.72/0.99  
% 3.72/0.99  --out_options                           all
% 3.72/0.99  --tptp_safe_out                         true
% 3.72/0.99  --problem_path                          ""
% 3.72/0.99  --include_path                          ""
% 3.72/0.99  --clausifier                            res/vclausify_rel
% 3.72/0.99  --clausifier_options                    ""
% 3.72/0.99  --stdin                                 false
% 3.72/0.99  --stats_out                             all
% 3.72/0.99  
% 3.72/0.99  ------ General Options
% 3.72/0.99  
% 3.72/0.99  --fof                                   false
% 3.72/0.99  --time_out_real                         305.
% 3.72/0.99  --time_out_virtual                      -1.
% 3.72/0.99  --symbol_type_check                     false
% 3.72/0.99  --clausify_out                          false
% 3.72/0.99  --sig_cnt_out                           false
% 3.72/0.99  --trig_cnt_out                          false
% 3.72/0.99  --trig_cnt_out_tolerance                1.
% 3.72/0.99  --trig_cnt_out_sk_spl                   false
% 3.72/0.99  --abstr_cl_out                          false
% 3.72/0.99  
% 3.72/0.99  ------ Global Options
% 3.72/0.99  
% 3.72/0.99  --schedule                              default
% 3.72/0.99  --add_important_lit                     false
% 3.72/0.99  --prop_solver_per_cl                    1000
% 3.72/0.99  --min_unsat_core                        false
% 3.72/0.99  --soft_assumptions                      false
% 3.72/0.99  --soft_lemma_size                       3
% 3.72/0.99  --prop_impl_unit_size                   0
% 3.72/0.99  --prop_impl_unit                        []
% 3.72/0.99  --share_sel_clauses                     true
% 3.72/0.99  --reset_solvers                         false
% 3.72/0.99  --bc_imp_inh                            [conj_cone]
% 3.72/0.99  --conj_cone_tolerance                   3.
% 3.72/0.99  --extra_neg_conj                        none
% 3.72/0.99  --large_theory_mode                     true
% 3.72/0.99  --prolific_symb_bound                   200
% 3.72/0.99  --lt_threshold                          2000
% 3.72/0.99  --clause_weak_htbl                      true
% 3.72/0.99  --gc_record_bc_elim                     false
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing Options
% 3.72/0.99  
% 3.72/0.99  --preprocessing_flag                    true
% 3.72/0.99  --time_out_prep_mult                    0.1
% 3.72/0.99  --splitting_mode                        input
% 3.72/0.99  --splitting_grd                         true
% 3.72/0.99  --splitting_cvd                         false
% 3.72/0.99  --splitting_cvd_svl                     false
% 3.72/0.99  --splitting_nvd                         32
% 3.72/0.99  --sub_typing                            true
% 3.72/0.99  --prep_gs_sim                           true
% 3.72/0.99  --prep_unflatten                        true
% 3.72/0.99  --prep_res_sim                          true
% 3.72/0.99  --prep_upred                            true
% 3.72/0.99  --prep_sem_filter                       exhaustive
% 3.72/0.99  --prep_sem_filter_out                   false
% 3.72/0.99  --pred_elim                             true
% 3.72/0.99  --res_sim_input                         true
% 3.72/0.99  --eq_ax_congr_red                       true
% 3.72/0.99  --pure_diseq_elim                       true
% 3.72/0.99  --brand_transform                       false
% 3.72/0.99  --non_eq_to_eq                          false
% 3.72/0.99  --prep_def_merge                        true
% 3.72/0.99  --prep_def_merge_prop_impl              false
% 3.72/0.99  --prep_def_merge_mbd                    true
% 3.72/0.99  --prep_def_merge_tr_red                 false
% 3.72/0.99  --prep_def_merge_tr_cl                  false
% 3.72/0.99  --smt_preprocessing                     true
% 3.72/0.99  --smt_ac_axioms                         fast
% 3.72/0.99  --preprocessed_out                      false
% 3.72/0.99  --preprocessed_stats                    false
% 3.72/0.99  
% 3.72/0.99  ------ Abstraction refinement Options
% 3.72/0.99  
% 3.72/0.99  --abstr_ref                             []
% 3.72/0.99  --abstr_ref_prep                        false
% 3.72/0.99  --abstr_ref_until_sat                   false
% 3.72/0.99  --abstr_ref_sig_restrict                funpre
% 3.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.99  --abstr_ref_under                       []
% 3.72/0.99  
% 3.72/0.99  ------ SAT Options
% 3.72/0.99  
% 3.72/0.99  --sat_mode                              false
% 3.72/0.99  --sat_fm_restart_options                ""
% 3.72/0.99  --sat_gr_def                            false
% 3.72/0.99  --sat_epr_types                         true
% 3.72/0.99  --sat_non_cyclic_types                  false
% 3.72/0.99  --sat_finite_models                     false
% 3.72/0.99  --sat_fm_lemmas                         false
% 3.72/0.99  --sat_fm_prep                           false
% 3.72/0.99  --sat_fm_uc_incr                        true
% 3.72/0.99  --sat_out_model                         small
% 3.72/0.99  --sat_out_clauses                       false
% 3.72/0.99  
% 3.72/0.99  ------ QBF Options
% 3.72/0.99  
% 3.72/0.99  --qbf_mode                              false
% 3.72/0.99  --qbf_elim_univ                         false
% 3.72/0.99  --qbf_dom_inst                          none
% 3.72/0.99  --qbf_dom_pre_inst                      false
% 3.72/0.99  --qbf_sk_in                             false
% 3.72/0.99  --qbf_pred_elim                         true
% 3.72/0.99  --qbf_split                             512
% 3.72/0.99  
% 3.72/0.99  ------ BMC1 Options
% 3.72/0.99  
% 3.72/0.99  --bmc1_incremental                      false
% 3.72/0.99  --bmc1_axioms                           reachable_all
% 3.72/0.99  --bmc1_min_bound                        0
% 3.72/0.99  --bmc1_max_bound                        -1
% 3.72/0.99  --bmc1_max_bound_default                -1
% 3.72/0.99  --bmc1_symbol_reachability              true
% 3.72/0.99  --bmc1_property_lemmas                  false
% 3.72/0.99  --bmc1_k_induction                      false
% 3.72/0.99  --bmc1_non_equiv_states                 false
% 3.72/0.99  --bmc1_deadlock                         false
% 3.72/0.99  --bmc1_ucm                              false
% 3.72/0.99  --bmc1_add_unsat_core                   none
% 3.72/0.99  --bmc1_unsat_core_children              false
% 3.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.99  --bmc1_out_stat                         full
% 3.72/0.99  --bmc1_ground_init                      false
% 3.72/0.99  --bmc1_pre_inst_next_state              false
% 3.72/0.99  --bmc1_pre_inst_state                   false
% 3.72/0.99  --bmc1_pre_inst_reach_state             false
% 3.72/0.99  --bmc1_out_unsat_core                   false
% 3.72/0.99  --bmc1_aig_witness_out                  false
% 3.72/0.99  --bmc1_verbose                          false
% 3.72/0.99  --bmc1_dump_clauses_tptp                false
% 3.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.99  --bmc1_dump_file                        -
% 3.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.99  --bmc1_ucm_extend_mode                  1
% 3.72/0.99  --bmc1_ucm_init_mode                    2
% 3.72/0.99  --bmc1_ucm_cone_mode                    none
% 3.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.99  --bmc1_ucm_relax_model                  4
% 3.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.99  --bmc1_ucm_layered_model                none
% 3.72/0.99  --bmc1_ucm_max_lemma_size               10
% 3.72/0.99  
% 3.72/0.99  ------ AIG Options
% 3.72/0.99  
% 3.72/0.99  --aig_mode                              false
% 3.72/0.99  
% 3.72/0.99  ------ Instantiation Options
% 3.72/0.99  
% 3.72/0.99  --instantiation_flag                    true
% 3.72/0.99  --inst_sos_flag                         true
% 3.72/0.99  --inst_sos_phase                        true
% 3.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.99  --inst_lit_sel_side                     none
% 3.72/0.99  --inst_solver_per_active                1400
% 3.72/0.99  --inst_solver_calls_frac                1.
% 3.72/0.99  --inst_passive_queue_type               priority_queues
% 3.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.99  --inst_passive_queues_freq              [25;2]
% 3.72/0.99  --inst_dismatching                      true
% 3.72/0.99  --inst_eager_unprocessed_to_passive     true
% 3.72/0.99  --inst_prop_sim_given                   true
% 3.72/0.99  --inst_prop_sim_new                     false
% 3.72/0.99  --inst_subs_new                         false
% 3.72/0.99  --inst_eq_res_simp                      false
% 3.72/0.99  --inst_subs_given                       false
% 3.72/0.99  --inst_orphan_elimination               true
% 3.72/0.99  --inst_learning_loop_flag               true
% 3.72/0.99  --inst_learning_start                   3000
% 3.72/0.99  --inst_learning_factor                  2
% 3.72/0.99  --inst_start_prop_sim_after_learn       3
% 3.72/0.99  --inst_sel_renew                        solver
% 3.72/0.99  --inst_lit_activity_flag                true
% 3.72/0.99  --inst_restr_to_given                   false
% 3.72/0.99  --inst_activity_threshold               500
% 3.72/0.99  --inst_out_proof                        true
% 3.72/0.99  
% 3.72/0.99  ------ Resolution Options
% 3.72/0.99  
% 3.72/0.99  --resolution_flag                       false
% 3.72/0.99  --res_lit_sel                           adaptive
% 3.72/0.99  --res_lit_sel_side                      none
% 3.72/0.99  --res_ordering                          kbo
% 3.72/0.99  --res_to_prop_solver                    active
% 3.72/0.99  --res_prop_simpl_new                    false
% 3.72/0.99  --res_prop_simpl_given                  true
% 3.72/0.99  --res_passive_queue_type                priority_queues
% 3.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.99  --res_passive_queues_freq               [15;5]
% 3.72/0.99  --res_forward_subs                      full
% 3.72/0.99  --res_backward_subs                     full
% 3.72/0.99  --res_forward_subs_resolution           true
% 3.72/0.99  --res_backward_subs_resolution          true
% 3.72/0.99  --res_orphan_elimination                true
% 3.72/0.99  --res_time_limit                        2.
% 3.72/0.99  --res_out_proof                         true
% 3.72/0.99  
% 3.72/0.99  ------ Superposition Options
% 3.72/0.99  
% 3.72/0.99  --superposition_flag                    true
% 3.72/0.99  --sup_passive_queue_type                priority_queues
% 3.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.99  --demod_completeness_check              fast
% 3.72/0.99  --demod_use_ground                      true
% 3.72/0.99  --sup_to_prop_solver                    passive
% 3.72/0.99  --sup_prop_simpl_new                    true
% 3.72/0.99  --sup_prop_simpl_given                  true
% 3.72/0.99  --sup_fun_splitting                     true
% 3.72/0.99  --sup_smt_interval                      50000
% 3.72/0.99  
% 3.72/0.99  ------ Superposition Simplification Setup
% 3.72/0.99  
% 3.72/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.72/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.72/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.72/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.72/0.99  --sup_immed_triv                        [TrivRules]
% 3.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_immed_bw_main                     []
% 3.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_input_bw                          []
% 3.72/0.99  
% 3.72/0.99  ------ Combination Options
% 3.72/0.99  
% 3.72/0.99  --comb_res_mult                         3
% 3.72/0.99  --comb_sup_mult                         2
% 3.72/0.99  --comb_inst_mult                        10
% 3.72/0.99  
% 3.72/0.99  ------ Debug Options
% 3.72/0.99  
% 3.72/0.99  --dbg_backtrace                         false
% 3.72/0.99  --dbg_dump_prop_clauses                 false
% 3.72/0.99  --dbg_dump_prop_clauses_file            -
% 3.72/0.99  --dbg_out_stat                          false
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS status Theorem for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99   Resolution empty clause
% 3.72/0.99  
% 3.72/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  fof(f16,conjecture,(
% 3.72/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f17,negated_conjecture,(
% 3.72/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.72/0.99    inference(negated_conjecture,[],[f16])).
% 3.72/0.99  
% 3.72/0.99  fof(f35,plain,(
% 3.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.72/0.99    inference(ennf_transformation,[],[f17])).
% 3.72/0.99  
% 3.72/0.99  fof(f36,plain,(
% 3.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.72/0.99    inference(flattening,[],[f35])).
% 3.72/0.99  
% 3.72/0.99  fof(f56,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f55,plain,(
% 3.72/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f54,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f53,plain,(
% 3.72/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f52,plain,(
% 3.72/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f51,plain,(
% 3.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f57,plain,(
% 3.72/0.99    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f36,f56,f55,f54,f53,f52,f51])).
% 3.72/0.99  
% 3.72/0.99  fof(f98,plain,(
% 3.72/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f12,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f28,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.99    inference(ennf_transformation,[],[f12])).
% 3.72/0.99  
% 3.72/0.99  fof(f78,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f28])).
% 3.72/0.99  
% 3.72/0.99  fof(f5,axiom,(
% 3.72/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f44,plain,(
% 3.72/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/0.99    inference(nnf_transformation,[],[f5])).
% 3.72/0.99  
% 3.72/0.99  fof(f45,plain,(
% 3.72/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/0.99    inference(flattening,[],[f44])).
% 3.72/0.99  
% 3.72/0.99  fof(f66,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.72/0.99    inference(cnf_transformation,[],[f45])).
% 3.72/0.99  
% 3.72/0.99  fof(f101,plain,(
% 3.72/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.72/0.99    inference(equality_resolution,[],[f66])).
% 3.72/0.99  
% 3.72/0.99  fof(f8,axiom,(
% 3.72/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f21,plain,(
% 3.72/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.72/0.99    inference(ennf_transformation,[],[f8])).
% 3.72/0.99  
% 3.72/0.99  fof(f47,plain,(
% 3.72/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.72/0.99    inference(nnf_transformation,[],[f21])).
% 3.72/0.99  
% 3.72/0.99  fof(f73,plain,(
% 3.72/0.99    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f47])).
% 3.72/0.99  
% 3.72/0.99  fof(f10,axiom,(
% 3.72/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f24,plain,(
% 3.72/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.72/0.99    inference(ennf_transformation,[],[f10])).
% 3.72/0.99  
% 3.72/0.99  fof(f25,plain,(
% 3.72/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.72/0.99    inference(flattening,[],[f24])).
% 3.72/0.99  
% 3.72/0.99  fof(f75,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f25])).
% 3.72/0.99  
% 3.72/0.99  fof(f3,axiom,(
% 3.72/0.99    v1_xboole_0(k1_xboole_0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f62,plain,(
% 3.72/0.99    v1_xboole_0(k1_xboole_0)),
% 3.72/0.99    inference(cnf_transformation,[],[f3])).
% 3.72/0.99  
% 3.72/0.99  fof(f4,axiom,(
% 3.72/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f18,plain,(
% 3.72/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(rectify,[],[f4])).
% 3.72/0.99  
% 3.72/0.99  fof(f19,plain,(
% 3.72/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(ennf_transformation,[],[f18])).
% 3.72/0.99  
% 3.72/0.99  fof(f42,plain,(
% 3.72/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f43,plain,(
% 3.72/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f42])).
% 3.72/0.99  
% 3.72/0.99  fof(f64,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f43])).
% 3.72/0.99  
% 3.72/0.99  fof(f1,axiom,(
% 3.72/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f37,plain,(
% 3.72/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.72/0.99    inference(nnf_transformation,[],[f1])).
% 3.72/0.99  
% 3.72/0.99  fof(f38,plain,(
% 3.72/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.72/0.99    inference(rectify,[],[f37])).
% 3.72/0.99  
% 3.72/0.99  fof(f39,plain,(
% 3.72/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f40,plain,(
% 3.72/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 3.72/0.99  
% 3.72/0.99  fof(f58,plain,(
% 3.72/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f40])).
% 3.72/0.99  
% 3.72/0.99  fof(f2,axiom,(
% 3.72/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f41,plain,(
% 3.72/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(nnf_transformation,[],[f2])).
% 3.72/0.99  
% 3.72/0.99  fof(f60,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f41])).
% 3.72/0.99  
% 3.72/0.99  fof(f61,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.72/0.99    inference(cnf_transformation,[],[f41])).
% 3.72/0.99  
% 3.72/0.99  fof(f9,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f22,plain,(
% 3.72/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.72/0.99    inference(ennf_transformation,[],[f9])).
% 3.72/0.99  
% 3.72/0.99  fof(f23,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 3.72/0.99    inference(flattening,[],[f22])).
% 3.72/0.99  
% 3.72/0.99  fof(f74,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f23])).
% 3.72/0.99  
% 3.72/0.99  fof(f91,plain,(
% 3.72/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f7,axiom,(
% 3.72/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f46,plain,(
% 3.72/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.72/0.99    inference(nnf_transformation,[],[f7])).
% 3.72/0.99  
% 3.72/0.99  fof(f70,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f46])).
% 3.72/0.99  
% 3.72/0.99  fof(f6,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f20,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f6])).
% 3.72/0.99  
% 3.72/0.99  fof(f69,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f20])).
% 3.72/0.99  
% 3.72/0.99  fof(f71,plain,(
% 3.72/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f46])).
% 3.72/0.99  
% 3.72/0.99  fof(f95,plain,(
% 3.72/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f13,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f29,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.72/0.99    inference(ennf_transformation,[],[f13])).
% 3.72/0.99  
% 3.72/0.99  fof(f30,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.72/0.99    inference(flattening,[],[f29])).
% 3.72/0.99  
% 3.72/0.99  fof(f79,plain,(
% 3.72/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f30])).
% 3.72/0.99  
% 3.72/0.99  fof(f93,plain,(
% 3.72/0.99    v1_funct_1(sK6)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f96,plain,(
% 3.72/0.99    v1_funct_1(sK7)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f14,axiom,(
% 3.72/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f31,plain,(
% 3.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.72/0.99    inference(ennf_transformation,[],[f14])).
% 3.72/0.99  
% 3.72/0.99  fof(f32,plain,(
% 3.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.72/0.99    inference(flattening,[],[f31])).
% 3.72/0.99  
% 3.72/0.99  fof(f49,plain,(
% 3.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.72/0.99    inference(nnf_transformation,[],[f32])).
% 3.72/0.99  
% 3.72/0.99  fof(f50,plain,(
% 3.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.72/0.99    inference(flattening,[],[f49])).
% 3.72/0.99  
% 3.72/0.99  fof(f80,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f50])).
% 3.72/0.99  
% 3.72/0.99  fof(f105,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(equality_resolution,[],[f80])).
% 3.72/0.99  
% 3.72/0.99  fof(f15,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f33,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f15])).
% 3.72/0.99  
% 3.72/0.99  fof(f34,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.72/0.99    inference(flattening,[],[f33])).
% 3.72/0.99  
% 3.72/0.99  fof(f83,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f34])).
% 3.72/0.99  
% 3.72/0.99  fof(f84,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f34])).
% 3.72/0.99  
% 3.72/0.99  fof(f85,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f34])).
% 3.72/0.99  
% 3.72/0.99  fof(f87,plain,(
% 3.72/0.99    ~v1_xboole_0(sK3)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f90,plain,(
% 3.72/0.99    ~v1_xboole_0(sK5)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f97,plain,(
% 3.72/0.99    v1_funct_2(sK7,sK5,sK3)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f88,plain,(
% 3.72/0.99    ~v1_xboole_0(sK4)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f94,plain,(
% 3.72/0.99    v1_funct_2(sK6,sK4,sK3)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f11,axiom,(
% 3.72/0.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f26,plain,(
% 3.72/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f11])).
% 3.72/0.99  
% 3.72/0.99  fof(f27,plain,(
% 3.72/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.72/0.99    inference(flattening,[],[f26])).
% 3.72/0.99  
% 3.72/0.99  fof(f48,plain,(
% 3.72/0.99    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.72/0.99    inference(nnf_transformation,[],[f27])).
% 3.72/0.99  
% 3.72/0.99  fof(f76,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f48])).
% 3.72/0.99  
% 3.72/0.99  fof(f92,plain,(
% 3.72/0.99    r1_subset_1(sK4,sK5)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f86,plain,(
% 3.72/0.99    ~v1_xboole_0(sK2)),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f89,plain,(
% 3.72/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f99,plain,(
% 3.72/0.99    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 3.72/0.99    inference(cnf_transformation,[],[f57])).
% 3.72/0.99  
% 3.72/0.99  fof(f81,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f50])).
% 3.72/0.99  
% 3.72/0.99  fof(f104,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(equality_resolution,[],[f81])).
% 3.72/0.99  
% 3.72/0.99  cnf(c_29,negated_conjecture,
% 3.72/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 3.72/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2142,plain,
% 3.72/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_20,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2148,plain,
% 3.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4175,plain,
% 3.72/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2142,c_2148]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_10,plain,
% 3.72/0.99      ( r1_tarski(X0,X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2152,plain,
% 3.72/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_14,plain,
% 3.72/0.99      ( v4_relat_1(X0,X1) | ~ r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_17,plain,
% 3.72/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_544,plain,
% 3.72/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.72/0.99      | ~ v1_relat_1(X0)
% 3.72/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.72/0.99      inference(resolution,[status(thm)],[c_14,c_17]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2127,plain,
% 3.72/0.99      ( k7_relat_1(X0,X1) = X0
% 3.72/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8414,plain,
% 3.72/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2152,c_2127]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8419,plain,
% 3.72/0.99      ( k7_relat_1(sK7,k1_relat_1(sK7)) = sK7 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_4175,c_8414]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4,plain,
% 3.72/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2157,plain,
% 3.72/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6,plain,
% 3.72/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2155,plain,
% 3.72/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.72/0.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1,plain,
% 3.72/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2160,plain,
% 3.72/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3584,plain,
% 3.72/0.99      ( r1_xboole_0(X0,X1) = iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2155,c_2160]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3,plain,
% 3.72/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2158,plain,
% 3.72/0.99      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6500,plain,
% 3.72/0.99      ( k3_xboole_0(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3584,c_2158]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6964,plain,
% 3.72/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2157,c_6500]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2,plain,
% 3.72/0.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2159,plain,
% 3.72/0.99      ( k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7276,plain,
% 3.72/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6964,c_2159]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_16,plain,
% 3.72/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.72/0.99      | ~ v1_relat_1(X2)
% 3.72/0.99      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2149,plain,
% 3.72/0.99      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 3.72/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7283,plain,
% 3.72/0.99      ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
% 3.72/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_7276,c_2149]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8057,plain,
% 3.72/0.99      ( k7_relat_1(k7_relat_1(sK7,X0),k1_xboole_0) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_4175,c_7283]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8487,plain,
% 3.72/0.99      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_8419,c_8057]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_36,negated_conjecture,
% 3.72/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2136,plain,
% 3.72/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_13,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2150,plain,
% 3.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.72/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3316,plain,
% 3.72/0.99      ( r1_tarski(sK5,sK2) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2136,c_2150]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_12,plain,
% 3.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_318,plain,
% 3.72/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.72/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_319,plain,
% 3.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_318]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_402,plain,
% 3.72/0.99      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.72/0.99      inference(bin_hyper_res,[status(thm)],[c_11,c_319]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2128,plain,
% 3.72/0.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.72/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3974,plain,
% 3.72/0.99      ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3316,c_2128]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_32,negated_conjecture,
% 3.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.72/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2139,plain,
% 3.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_21,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.72/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2147,plain,
% 3.72/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4579,plain,
% 3.72/0.99      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
% 3.72/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2139,c_2147]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_34,negated_conjecture,
% 3.72/0.99      ( v1_funct_1(sK6) ),
% 3.72/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_49,plain,
% 3.72/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6207,plain,
% 3.72/0.99      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.72/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4579,c_49]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4578,plain,
% 3.72/0.99      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
% 3.72/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2142,c_2147]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_31,negated_conjecture,
% 3.72/0.99      ( v1_funct_1(sK7) ),
% 3.72/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_52,plain,
% 3.72/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6186,plain,
% 3.72/0.99      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
% 3.72/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4578,c_52]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_24,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.72/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_27,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_26,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_25,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_228,plain,
% 3.72/0.99      ( ~ v1_funct_1(X3)
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_24,c_27,c_26,c_25]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_229,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_228]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2130,plain,
% 3.72/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.72/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.72/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.72/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.72/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top
% 3.72/0.99      | v1_funct_1(X5) != iProver_top
% 3.72/0.99      | v1_xboole_0(X3) = iProver_top
% 3.72/0.99      | v1_xboole_0(X4) = iProver_top
% 3.72/0.99      | v1_xboole_0(X1) = iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6190,plain,
% 3.72/0.99      ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.72/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.72/0.99      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.72/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | v1_funct_1(X1) != iProver_top
% 3.72/0.99      | v1_funct_1(sK7) != iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top
% 3.72/0.99      | v1_xboole_0(X2) = iProver_top
% 3.72/0.99      | v1_xboole_0(sK3) = iProver_top
% 3.72/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6186,c_2130]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_40,negated_conjecture,
% 3.72/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.72/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_43,plain,
% 3.72/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_37,negated_conjecture,
% 3.72/0.99      ( ~ v1_xboole_0(sK5) ),
% 3.72/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_46,plain,
% 3.72/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_30,negated_conjecture,
% 3.72/0.99      ( v1_funct_2(sK7,sK5,sK3) ),
% 3.72/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_53,plain,
% 3.72/0.99      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_54,plain,
% 3.72/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6343,plain,
% 3.72/0.99      ( v1_funct_1(X1) != iProver_top
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.72/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.72/0.99      | k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.72/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top
% 3.72/0.99      | v1_xboole_0(X2) = iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6190,c_43,c_46,c_52,c_53,c_54]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6344,plain,
% 3.72/0.99      ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.72/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.72/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | v1_funct_1(X1) != iProver_top
% 3.72/0.99      | v1_xboole_0(X2) = iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_6343]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6350,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.72/0.99      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.72/0.99      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.72/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | v1_funct_1(sK6) != iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top
% 3.72/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6207,c_6344]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_39,negated_conjecture,
% 3.72/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.72/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_44,plain,
% 3.72/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_33,negated_conjecture,
% 3.72/0.99      ( v1_funct_2(sK6,sK4,sK3) ),
% 3.72/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_50,plain,
% 3.72/0.99      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_51,plain,
% 3.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6574,plain,
% 3.72/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.72/0.99      | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.72/0.99      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6350,c_44,c_49,c_50,c_51]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6575,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.72/0.99      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_6574]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6581,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.72/0.99      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3974,c_6575]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_19,plain,
% 3.72/0.99      ( ~ r1_subset_1(X0,X1)
% 3.72/0.99      | r1_xboole_0(X0,X1)
% 3.72/0.99      | v1_xboole_0(X0)
% 3.72/0.99      | v1_xboole_0(X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_35,negated_conjecture,
% 3.72/0.99      ( r1_subset_1(sK4,sK5) ),
% 3.72/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_599,plain,
% 3.72/0.99      ( r1_xboole_0(X0,X1)
% 3.72/0.99      | v1_xboole_0(X0)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | sK5 != X1
% 3.72/0.99      | sK4 != X0 ),
% 3.72/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_600,plain,
% 3.72/0.99      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 3.72/0.99      inference(unflattening,[status(thm)],[c_599]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_602,plain,
% 3.72/0.99      ( r1_xboole_0(sK4,sK5) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_600,c_39,c_37]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2126,plain,
% 3.72/0.99      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3139,plain,
% 3.72/0.99      ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2126,c_2158]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6582,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.72/0.99      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_6581,c_3139]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6583,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.72/0.99      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_6582,c_3974]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6584,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.72/0.99      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_6583,c_3139]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_41,negated_conjecture,
% 3.72/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.72/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_38,negated_conjecture,
% 3.72/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_28,negated_conjecture,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.72/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.72/0.99      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4061,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.72/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.72/0.99      | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_3974,c_28]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4062,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.72/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.72/0.99      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_4061,c_3139]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6189,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.72/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.72/0.99      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_6186,c_4062]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6279,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.72/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.72/0.99      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_6189,c_6207]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6588,plain,
% 3.72/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 3.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 3.72/0.99      | v1_xboole_0(sK2)
% 3.72/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.72/0.99      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.72/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6584]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_23,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_235,plain,
% 3.72/0.99      ( ~ v1_funct_1(X3)
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_23,c_27,c_26,c_25]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_236,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.72/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | v1_xboole_0(X2)
% 3.72/0.99      | v1_xboole_0(X4)
% 3.72/0.99      | v1_xboole_0(X5)
% 3.72/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_235]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2129,plain,
% 3.72/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.72/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.72/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.72/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.72/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top
% 3.72/0.99      | v1_funct_1(X5) != iProver_top
% 3.72/0.99      | v1_xboole_0(X3) = iProver_top
% 3.72/0.99      | v1_xboole_0(X4) = iProver_top
% 3.72/0.99      | v1_xboole_0(X1) = iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6191,plain,
% 3.72/0.99      ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.72/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.72/0.99      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.72/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | v1_funct_1(X1) != iProver_top
% 3.72/0.99      | v1_funct_1(sK7) != iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top
% 3.72/0.99      | v1_xboole_0(X2) = iProver_top
% 3.72/0.99      | v1_xboole_0(sK3) = iProver_top
% 3.72/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6186,c_2129]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6631,plain,
% 3.72/0.99      ( v1_funct_1(X1) != iProver_top
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.72/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.72/0.99      | k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.72/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top
% 3.72/0.99      | v1_xboole_0(X2) = iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6191,c_43,c_46,c_52,c_53,c_54]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6632,plain,
% 3.72/0.99      ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.72/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.72/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.72/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.72/0.99      | v1_funct_1(X1) != iProver_top
% 3.72/0.99      | v1_xboole_0(X2) = iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_6631]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6638,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.72/0.99      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.72/0.99      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.72/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | v1_funct_1(sK6) != iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top
% 3.72/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6207,c_6632]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6653,plain,
% 3.72/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.72/0.99      | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.72/0.99      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6638,c_44,c_49,c_50,c_51]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6654,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.72/0.99      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_6653]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6660,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.72/0.99      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3974,c_6654]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6661,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.72/0.99      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_6660,c_3139]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6662,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.72/0.99      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_6661,c_3974]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6663,plain,
% 3.72/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.72/0.99      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 3.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.72/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_6662,c_3139]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6667,plain,
% 3.72/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 3.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 3.72/0.99      | v1_xboole_0(sK2)
% 3.72/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.72/0.99      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.72/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6663]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7574,plain,
% 3.72/0.99      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6584,c_41,c_38,c_36,c_6279,c_6588,c_6667]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8840,plain,
% 3.72/0.99      ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_8487,c_7574]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4176,plain,
% 3.72/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2139,c_2148]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8420,plain,
% 3.72/0.99      ( k7_relat_1(sK6,k1_relat_1(sK6)) = sK6 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_4176,c_8414]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8058,plain,
% 3.72/0.99      ( k7_relat_1(k7_relat_1(sK6,X0),k1_xboole_0) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_4176,c_7283]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8836,plain,
% 3.72/0.99      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_8420,c_8058]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8841,plain,
% 3.72/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_8840,c_8836]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8842,plain,
% 3.72/0.99      ( $false ),
% 3.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_8841]) ).
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  ------                               Statistics
% 3.72/0.99  
% 3.72/0.99  ------ General
% 3.72/0.99  
% 3.72/0.99  abstr_ref_over_cycles:                  0
% 3.72/0.99  abstr_ref_under_cycles:                 0
% 3.72/0.99  gc_basic_clause_elim:                   0
% 3.72/0.99  forced_gc_time:                         0
% 3.72/0.99  parsing_time:                           0.01
% 3.72/0.99  unif_index_cands_time:                  0.
% 3.72/0.99  unif_index_add_time:                    0.
% 3.72/0.99  orderings_time:                         0.
% 3.72/0.99  out_proof_time:                         0.015
% 3.72/0.99  total_time:                             0.501
% 3.72/0.99  num_of_symbols:                         59
% 3.72/0.99  num_of_terms:                           19920
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing
% 3.72/0.99  
% 3.72/0.99  num_of_splits:                          0
% 3.72/0.99  num_of_split_atoms:                     0
% 3.72/0.99  num_of_reused_defs:                     0
% 3.72/0.99  num_eq_ax_congr_red:                    34
% 3.72/0.99  num_of_sem_filtered_clauses:            1
% 3.72/0.99  num_of_subtypes:                        0
% 3.72/0.99  monotx_restored_types:                  0
% 3.72/0.99  sat_num_of_epr_types:                   0
% 3.72/0.99  sat_num_of_non_cyclic_types:            0
% 3.72/0.99  sat_guarded_non_collapsed_types:        0
% 3.72/0.99  num_pure_diseq_elim:                    0
% 3.72/0.99  simp_replaced_by:                       0
% 3.72/0.99  res_preprocessed:                       185
% 3.72/0.99  prep_upred:                             0
% 3.72/0.99  prep_unflattend:                        16
% 3.72/0.99  smt_new_axioms:                         0
% 3.72/0.99  pred_elim_cands:                        8
% 3.72/0.99  pred_elim:                              2
% 3.72/0.99  pred_elim_cl:                           4
% 3.72/0.99  pred_elim_cycles:                       6
% 3.72/0.99  merged_defs:                            16
% 3.72/0.99  merged_defs_ncl:                        0
% 3.72/0.99  bin_hyper_res:                          17
% 3.72/0.99  prep_cycles:                            4
% 3.72/0.99  pred_elim_time:                         0.005
% 3.72/0.99  splitting_time:                         0.
% 3.72/0.99  sem_filter_time:                        0.
% 3.72/0.99  monotx_time:                            0.
% 3.72/0.99  subtype_inf_time:                       0.
% 3.72/0.99  
% 3.72/0.99  ------ Problem properties
% 3.72/0.99  
% 3.72/0.99  clauses:                                37
% 3.72/0.99  conjectures:                            13
% 3.72/0.99  epr:                                    14
% 3.72/0.99  horn:                                   28
% 3.72/0.99  ground:                                 15
% 3.72/0.99  unary:                                  15
% 3.72/0.99  binary:                                 10
% 3.72/0.99  lits:                                   137
% 3.72/0.99  lits_eq:                                16
% 3.72/0.99  fd_pure:                                0
% 3.72/0.99  fd_pseudo:                              0
% 3.72/0.99  fd_cond:                                0
% 3.72/0.99  fd_pseudo_cond:                         1
% 3.72/0.99  ac_symbols:                             0
% 3.72/0.99  
% 3.72/0.99  ------ Propositional Solver
% 3.72/0.99  
% 3.72/0.99  prop_solver_calls:                      29
% 3.72/0.99  prop_fast_solver_calls:                 2223
% 3.72/0.99  smt_solver_calls:                       0
% 3.72/0.99  smt_fast_solver_calls:                  0
% 3.72/0.99  prop_num_of_clauses:                    4350
% 3.72/0.99  prop_preprocess_simplified:             10828
% 3.72/0.99  prop_fo_subsumed:                       136
% 3.72/0.99  prop_solver_time:                       0.
% 3.72/0.99  smt_solver_time:                        0.
% 3.72/0.99  smt_fast_solver_time:                   0.
% 3.72/0.99  prop_fast_solver_time:                  0.
% 3.72/0.99  prop_unsat_core_time:                   0.
% 3.72/0.99  
% 3.72/0.99  ------ QBF
% 3.72/0.99  
% 3.72/0.99  qbf_q_res:                              0
% 3.72/0.99  qbf_num_tautologies:                    0
% 3.72/0.99  qbf_prep_cycles:                        0
% 3.72/0.99  
% 3.72/0.99  ------ BMC1
% 3.72/0.99  
% 3.72/0.99  bmc1_current_bound:                     -1
% 3.72/0.99  bmc1_last_solved_bound:                 -1
% 3.72/0.99  bmc1_unsat_core_size:                   -1
% 3.72/0.99  bmc1_unsat_core_parents_size:           -1
% 3.72/0.99  bmc1_merge_next_fun:                    0
% 3.72/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.72/0.99  
% 3.72/0.99  ------ Instantiation
% 3.72/0.99  
% 3.72/0.99  inst_num_of_clauses:                    1082
% 3.72/0.99  inst_num_in_passive:                    535
% 3.72/0.99  inst_num_in_active:                     541
% 3.72/0.99  inst_num_in_unprocessed:                6
% 3.72/0.99  inst_num_of_loops:                      630
% 3.72/0.99  inst_num_of_learning_restarts:          0
% 3.72/0.99  inst_num_moves_active_passive:          87
% 3.72/0.99  inst_lit_activity:                      0
% 3.72/0.99  inst_lit_activity_moves:                1
% 3.72/0.99  inst_num_tautologies:                   0
% 3.72/0.99  inst_num_prop_implied:                  0
% 3.72/0.99  inst_num_existing_simplified:           0
% 3.72/0.99  inst_num_eq_res_simplified:             0
% 3.72/0.99  inst_num_child_elim:                    0
% 3.72/0.99  inst_num_of_dismatching_blockings:      170
% 3.72/0.99  inst_num_of_non_proper_insts:           1101
% 3.72/0.99  inst_num_of_duplicates:                 0
% 3.72/0.99  inst_inst_num_from_inst_to_res:         0
% 3.72/0.99  inst_dismatching_checking_time:         0.
% 3.72/0.99  
% 3.72/0.99  ------ Resolution
% 3.72/0.99  
% 3.72/0.99  res_num_of_clauses:                     0
% 3.72/0.99  res_num_in_passive:                     0
% 3.72/0.99  res_num_in_active:                      0
% 3.72/0.99  res_num_of_loops:                       189
% 3.72/0.99  res_forward_subset_subsumed:            35
% 3.72/0.99  res_backward_subset_subsumed:           0
% 3.72/0.99  res_forward_subsumed:                   0
% 3.72/0.99  res_backward_subsumed:                  0
% 3.72/0.99  res_forward_subsumption_resolution:     0
% 3.72/0.99  res_backward_subsumption_resolution:    0
% 3.72/0.99  res_clause_to_clause_subsumption:       475
% 3.72/0.99  res_orphan_elimination:                 0
% 3.72/0.99  res_tautology_del:                      48
% 3.72/0.99  res_num_eq_res_simplified:              0
% 3.72/0.99  res_num_sel_changes:                    0
% 3.72/0.99  res_moves_from_active_to_pass:          0
% 3.72/0.99  
% 3.72/0.99  ------ Superposition
% 3.72/0.99  
% 3.72/0.99  sup_time_total:                         0.
% 3.72/0.99  sup_time_generating:                    0.
% 3.72/0.99  sup_time_sim_full:                      0.
% 3.72/0.99  sup_time_sim_immed:                     0.
% 3.72/0.99  
% 3.72/0.99  sup_num_of_clauses:                     179
% 3.72/0.99  sup_num_in_active:                      118
% 3.72/0.99  sup_num_in_passive:                     61
% 3.72/0.99  sup_num_of_loops:                       125
% 3.72/0.99  sup_fw_superposition:                   165
% 3.72/0.99  sup_bw_superposition:                   51
% 3.72/0.99  sup_immediate_simplified:               103
% 3.72/0.99  sup_given_eliminated:                   0
% 3.72/0.99  comparisons_done:                       0
% 3.72/0.99  comparisons_avoided:                    0
% 3.72/0.99  
% 3.72/0.99  ------ Simplifications
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  sim_fw_subset_subsumed:                 16
% 3.72/0.99  sim_bw_subset_subsumed:                 0
% 3.72/0.99  sim_fw_subsumed:                        14
% 3.72/0.99  sim_bw_subsumed:                        3
% 3.72/0.99  sim_fw_subsumption_res:                 0
% 3.72/0.99  sim_bw_subsumption_res:                 0
% 3.72/0.99  sim_tautology_del:                      2
% 3.72/0.99  sim_eq_tautology_del:                   1
% 3.72/0.99  sim_eq_res_simp:                        0
% 3.72/0.99  sim_fw_demodulated:                     49
% 3.72/0.99  sim_bw_demodulated:                     6
% 3.72/0.99  sim_light_normalised:                   43
% 3.72/0.99  sim_joinable_taut:                      0
% 3.72/0.99  sim_joinable_simp:                      0
% 3.72/0.99  sim_ac_normalised:                      0
% 3.72/0.99  sim_smt_subsumption:                    0
% 3.72/0.99  
%------------------------------------------------------------------------------
