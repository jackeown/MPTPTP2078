%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:39 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  178 (1509 expanded)
%              Number of clauses        :  105 ( 335 expanded)
%              Number of leaves         :   19 ( 611 expanded)
%              Depth                    :   26
%              Number of atoms          : 1077 (20075 expanded)
%              Number of equality atoms :  408 (4773 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f30,f43,f42,f41,f40,f39,f38])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
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
    inference(equality_resolution,[],[f58])).

fof(f10,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
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

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1458,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1466,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3729,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1458,c_1466])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1853,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2037,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_4088,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3729,c_25,c_23,c_2037])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1461,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3728,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_1466])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1848,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0,X1,sK7,X2) = k7_relat_1(sK7,X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2028,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_3876,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3728,c_22,c_20,c_2028])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1455,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1467,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2751,plain,
    ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_1455,c_1467])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_178,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_18,c_17,c_16])).

cnf(c_179,plain,
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
    inference(renaming,[status(thm)],[c_178])).

cnf(c_1449,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_179])).

cnf(c_3414,plain,
    ( k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
    | k2_partfun1(sK5,X1,X3,k9_subset_1(sK2,X0,sK5)) != k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5))
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2751,c_1449])).

cnf(c_3460,plain,
    ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3414,c_2751])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_33,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_37,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6468,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
    | k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3460,c_33,c_37,c_38])).

cnf(c_6469,plain,
    ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6468])).

cnf(c_6487,plain,
    ( k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3876,c_6469])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_34,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_43,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_44,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6750,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6487,c_34,c_43,c_44,c_45])).

cnf(c_6751,plain,
    ( k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6750])).

cnf(c_6764,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_6751])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11,c_8])).

cnf(c_1447,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_2313,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1461,c_1447])).

cnf(c_2314,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1458,c_1447])).

cnf(c_10,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_371,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_372,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_374,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_30,c_28])).

cnf(c_1446,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1472,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1471,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2641,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1471])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1469,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5294,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_1469])).

cnf(c_5302,plain,
    ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1446,c_5294])).

cnf(c_6788,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6764,c_2313,c_2314,c_5302])).

cnf(c_6789,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6788])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_185,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_18,c_17,c_16])).

cnf(c_186,plain,
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
    inference(renaming,[status(thm)],[c_185])).

cnf(c_1448,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_2768,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(sK2,X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2751,c_1448])).

cnf(c_2783,plain,
    ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2768,c_2751])).

cnf(c_3246,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
    | k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2783,c_33,c_37,c_38])).

cnf(c_3247,plain,
    ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK5,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3246])).

cnf(c_3886,plain,
    ( k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3876,c_3247])).

cnf(c_4723,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_34,c_43,c_44,c_45])).

cnf(c_4724,plain,
    ( k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4723])).

cnf(c_4737,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_4724])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4752,plain,
    ( ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK4)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4737])).

cnf(c_4795,plain,
    ( k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4737,c_30,c_29,c_25,c_24,c_23,c_4752])).

cnf(c_4796,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_4795])).

cnf(c_5372,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5302,c_4796])).

cnf(c_5383,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5372,c_2313,c_2314])).

cnf(c_5384,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_5383])).

cnf(c_19,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2766,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_2751,c_19])).

cnf(c_3880,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_3876,c_2766])).

cnf(c_4307,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_3880,c_4088])).

cnf(c_5373,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5302,c_4307])).

cnf(c_5377,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5373,c_2313,c_2314])).

cnf(c_5378,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_5377])).

cnf(c_5386,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5384,c_5378])).

cnf(c_42,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_40,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_35,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6789,c_5386,c_42,c_41,c_40,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:29:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.70/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.98  
% 3.70/0.98  ------  iProver source info
% 3.70/0.98  
% 3.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.98  git: non_committed_changes: false
% 3.70/0.98  git: last_make_outside_of_git: false
% 3.70/0.98  
% 3.70/0.98  ------ 
% 3.70/0.98  
% 3.70/0.98  ------ Input Options
% 3.70/0.98  
% 3.70/0.98  --out_options                           all
% 3.70/0.98  --tptp_safe_out                         true
% 3.70/0.98  --problem_path                          ""
% 3.70/0.98  --include_path                          ""
% 3.70/0.98  --clausifier                            res/vclausify_rel
% 3.70/0.98  --clausifier_options                    --mode clausify
% 3.70/0.98  --stdin                                 false
% 3.70/0.98  --stats_out                             all
% 3.70/0.98  
% 3.70/0.98  ------ General Options
% 3.70/0.98  
% 3.70/0.98  --fof                                   false
% 3.70/0.98  --time_out_real                         305.
% 3.70/0.98  --time_out_virtual                      -1.
% 3.70/0.98  --symbol_type_check                     false
% 3.70/0.98  --clausify_out                          false
% 3.70/0.98  --sig_cnt_out                           false
% 3.70/0.98  --trig_cnt_out                          false
% 3.70/0.98  --trig_cnt_out_tolerance                1.
% 3.70/0.98  --trig_cnt_out_sk_spl                   false
% 3.70/0.98  --abstr_cl_out                          false
% 3.70/0.98  
% 3.70/0.98  ------ Global Options
% 3.70/0.98  
% 3.70/0.98  --schedule                              default
% 3.70/0.98  --add_important_lit                     false
% 3.70/0.98  --prop_solver_per_cl                    1000
% 3.70/0.98  --min_unsat_core                        false
% 3.70/0.98  --soft_assumptions                      false
% 3.70/0.98  --soft_lemma_size                       3
% 3.70/0.98  --prop_impl_unit_size                   0
% 3.70/0.98  --prop_impl_unit                        []
% 3.70/0.98  --share_sel_clauses                     true
% 3.70/0.98  --reset_solvers                         false
% 3.70/0.98  --bc_imp_inh                            [conj_cone]
% 3.70/0.98  --conj_cone_tolerance                   3.
% 3.70/0.98  --extra_neg_conj                        none
% 3.70/0.98  --large_theory_mode                     true
% 3.70/0.98  --prolific_symb_bound                   200
% 3.70/0.98  --lt_threshold                          2000
% 3.70/0.98  --clause_weak_htbl                      true
% 3.70/0.98  --gc_record_bc_elim                     false
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing Options
% 3.70/0.98  
% 3.70/0.98  --preprocessing_flag                    true
% 3.70/0.98  --time_out_prep_mult                    0.1
% 3.70/0.98  --splitting_mode                        input
% 3.70/0.98  --splitting_grd                         true
% 3.70/0.98  --splitting_cvd                         false
% 3.70/0.98  --splitting_cvd_svl                     false
% 3.70/0.98  --splitting_nvd                         32
% 3.70/0.98  --sub_typing                            true
% 3.70/0.98  --prep_gs_sim                           true
% 3.70/0.98  --prep_unflatten                        true
% 3.70/0.98  --prep_res_sim                          true
% 3.70/0.98  --prep_upred                            true
% 3.70/0.98  --prep_sem_filter                       exhaustive
% 3.70/0.98  --prep_sem_filter_out                   false
% 3.70/0.98  --pred_elim                             true
% 3.70/0.98  --res_sim_input                         true
% 3.70/0.98  --eq_ax_congr_red                       true
% 3.70/0.98  --pure_diseq_elim                       true
% 3.70/0.98  --brand_transform                       false
% 3.70/0.98  --non_eq_to_eq                          false
% 3.70/0.98  --prep_def_merge                        true
% 3.70/0.98  --prep_def_merge_prop_impl              false
% 3.70/0.98  --prep_def_merge_mbd                    true
% 3.70/0.98  --prep_def_merge_tr_red                 false
% 3.70/0.98  --prep_def_merge_tr_cl                  false
% 3.70/0.98  --smt_preprocessing                     true
% 3.70/0.98  --smt_ac_axioms                         fast
% 3.70/0.98  --preprocessed_out                      false
% 3.70/0.98  --preprocessed_stats                    false
% 3.70/0.98  
% 3.70/0.98  ------ Abstraction refinement Options
% 3.70/0.98  
% 3.70/0.98  --abstr_ref                             []
% 3.70/0.98  --abstr_ref_prep                        false
% 3.70/0.98  --abstr_ref_until_sat                   false
% 3.70/0.98  --abstr_ref_sig_restrict                funpre
% 3.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.98  --abstr_ref_under                       []
% 3.70/0.98  
% 3.70/0.98  ------ SAT Options
% 3.70/0.98  
% 3.70/0.98  --sat_mode                              false
% 3.70/0.98  --sat_fm_restart_options                ""
% 3.70/0.98  --sat_gr_def                            false
% 3.70/0.98  --sat_epr_types                         true
% 3.70/0.98  --sat_non_cyclic_types                  false
% 3.70/0.98  --sat_finite_models                     false
% 3.70/0.98  --sat_fm_lemmas                         false
% 3.70/0.98  --sat_fm_prep                           false
% 3.70/0.98  --sat_fm_uc_incr                        true
% 3.70/0.98  --sat_out_model                         small
% 3.70/0.98  --sat_out_clauses                       false
% 3.70/0.98  
% 3.70/0.98  ------ QBF Options
% 3.70/0.98  
% 3.70/0.98  --qbf_mode                              false
% 3.70/0.98  --qbf_elim_univ                         false
% 3.70/0.98  --qbf_dom_inst                          none
% 3.70/0.98  --qbf_dom_pre_inst                      false
% 3.70/0.98  --qbf_sk_in                             false
% 3.70/0.98  --qbf_pred_elim                         true
% 3.70/0.98  --qbf_split                             512
% 3.70/0.98  
% 3.70/0.98  ------ BMC1 Options
% 3.70/0.98  
% 3.70/0.98  --bmc1_incremental                      false
% 3.70/0.98  --bmc1_axioms                           reachable_all
% 3.70/0.98  --bmc1_min_bound                        0
% 3.70/0.98  --bmc1_max_bound                        -1
% 3.70/0.98  --bmc1_max_bound_default                -1
% 3.70/0.98  --bmc1_symbol_reachability              true
% 3.70/0.98  --bmc1_property_lemmas                  false
% 3.70/0.98  --bmc1_k_induction                      false
% 3.70/0.98  --bmc1_non_equiv_states                 false
% 3.70/0.98  --bmc1_deadlock                         false
% 3.70/0.98  --bmc1_ucm                              false
% 3.70/0.98  --bmc1_add_unsat_core                   none
% 3.70/0.98  --bmc1_unsat_core_children              false
% 3.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.98  --bmc1_out_stat                         full
% 3.70/0.98  --bmc1_ground_init                      false
% 3.70/0.98  --bmc1_pre_inst_next_state              false
% 3.70/0.98  --bmc1_pre_inst_state                   false
% 3.70/0.98  --bmc1_pre_inst_reach_state             false
% 3.70/0.98  --bmc1_out_unsat_core                   false
% 3.70/0.98  --bmc1_aig_witness_out                  false
% 3.70/0.98  --bmc1_verbose                          false
% 3.70/0.98  --bmc1_dump_clauses_tptp                false
% 3.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.98  --bmc1_dump_file                        -
% 3.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.98  --bmc1_ucm_extend_mode                  1
% 3.70/0.98  --bmc1_ucm_init_mode                    2
% 3.70/0.98  --bmc1_ucm_cone_mode                    none
% 3.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.98  --bmc1_ucm_relax_model                  4
% 3.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.98  --bmc1_ucm_layered_model                none
% 3.70/0.98  --bmc1_ucm_max_lemma_size               10
% 3.70/0.98  
% 3.70/0.98  ------ AIG Options
% 3.70/0.98  
% 3.70/0.98  --aig_mode                              false
% 3.70/0.98  
% 3.70/0.98  ------ Instantiation Options
% 3.70/0.98  
% 3.70/0.98  --instantiation_flag                    true
% 3.70/0.98  --inst_sos_flag                         false
% 3.70/0.98  --inst_sos_phase                        true
% 3.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.98  --inst_lit_sel_side                     num_symb
% 3.70/0.98  --inst_solver_per_active                1400
% 3.70/0.98  --inst_solver_calls_frac                1.
% 3.70/0.98  --inst_passive_queue_type               priority_queues
% 3.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.98  --inst_passive_queues_freq              [25;2]
% 3.70/0.98  --inst_dismatching                      true
% 3.70/0.98  --inst_eager_unprocessed_to_passive     true
% 3.70/0.98  --inst_prop_sim_given                   true
% 3.70/0.98  --inst_prop_sim_new                     false
% 3.70/0.98  --inst_subs_new                         false
% 3.70/0.98  --inst_eq_res_simp                      false
% 3.70/0.98  --inst_subs_given                       false
% 3.70/0.98  --inst_orphan_elimination               true
% 3.70/0.98  --inst_learning_loop_flag               true
% 3.70/0.98  --inst_learning_start                   3000
% 3.70/0.98  --inst_learning_factor                  2
% 3.70/0.98  --inst_start_prop_sim_after_learn       3
% 3.70/0.98  --inst_sel_renew                        solver
% 3.70/0.98  --inst_lit_activity_flag                true
% 3.70/0.98  --inst_restr_to_given                   false
% 3.70/0.98  --inst_activity_threshold               500
% 3.70/0.98  --inst_out_proof                        true
% 3.70/0.98  
% 3.70/0.98  ------ Resolution Options
% 3.70/0.98  
% 3.70/0.98  --resolution_flag                       true
% 3.70/0.98  --res_lit_sel                           adaptive
% 3.70/0.98  --res_lit_sel_side                      none
% 3.70/0.98  --res_ordering                          kbo
% 3.70/0.98  --res_to_prop_solver                    active
% 3.70/0.98  --res_prop_simpl_new                    false
% 3.70/0.98  --res_prop_simpl_given                  true
% 3.70/0.98  --res_passive_queue_type                priority_queues
% 3.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     false
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   []
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_full_bw                           [BwDemod]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  ------ Parsing...
% 3.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  ------ Proving...
% 3.70/0.99  ------ Problem Properties 
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  clauses                                 30
% 3.70/0.99  conjectures                             13
% 3.70/0.99  EPR                                     12
% 3.70/0.99  Horn                                    21
% 3.70/0.99  unary                                   14
% 3.70/0.99  binary                                  7
% 3.70/0.99  lits                                    121
% 3.70/0.99  lits eq                                 13
% 3.70/0.99  fd_pure                                 0
% 3.70/0.99  fd_pseudo                               0
% 3.70/0.99  fd_cond                                 1
% 3.70/0.99  fd_pseudo_cond                          0
% 3.70/0.99  AC symbols                              0
% 3.70/0.99  
% 3.70/0.99  ------ Schedule dynamic 5 is on 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  Current options:
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    --mode clausify
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/0.99  --bmc1_deadlock                         false
% 3.70/0.99  --bmc1_ucm                              false
% 3.70/0.99  --bmc1_add_unsat_core                   none
% 3.70/0.99  --bmc1_unsat_core_children              false
% 3.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.99  --bmc1_out_stat                         full
% 3.70/0.99  --bmc1_ground_init                      false
% 3.70/0.99  --bmc1_pre_inst_next_state              false
% 3.70/0.99  --bmc1_pre_inst_state                   false
% 3.70/0.99  --bmc1_pre_inst_reach_state             false
% 3.70/0.99  --bmc1_out_unsat_core                   false
% 3.70/0.99  --bmc1_aig_witness_out                  false
% 3.70/0.99  --bmc1_verbose                          false
% 3.70/0.99  --bmc1_dump_clauses_tptp                false
% 3.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.99  --bmc1_dump_file                        -
% 3.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.99  --bmc1_ucm_extend_mode                  1
% 3.70/0.99  --bmc1_ucm_init_mode                    2
% 3.70/0.99  --bmc1_ucm_cone_mode                    none
% 3.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.99  --bmc1_ucm_relax_model                  4
% 3.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.99  --bmc1_ucm_layered_model                none
% 3.70/0.99  --bmc1_ucm_max_lemma_size               10
% 3.70/0.99  
% 3.70/0.99  ------ AIG Options
% 3.70/0.99  
% 3.70/0.99  --aig_mode                              false
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation Options
% 3.70/0.99  
% 3.70/0.99  --instantiation_flag                    true
% 3.70/0.99  --inst_sos_flag                         false
% 3.70/0.99  --inst_sos_phase                        true
% 3.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel_side                     none
% 3.70/0.99  --inst_solver_per_active                1400
% 3.70/0.99  --inst_solver_calls_frac                1.
% 3.70/0.99  --inst_passive_queue_type               priority_queues
% 3.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.99  --inst_passive_queues_freq              [25;2]
% 3.70/0.99  --inst_dismatching                      true
% 3.70/0.99  --inst_eager_unprocessed_to_passive     true
% 3.70/0.99  --inst_prop_sim_given                   true
% 3.70/0.99  --inst_prop_sim_new                     false
% 3.70/0.99  --inst_subs_new                         false
% 3.70/0.99  --inst_eq_res_simp                      false
% 3.70/0.99  --inst_subs_given                       false
% 3.70/0.99  --inst_orphan_elimination               true
% 3.70/0.99  --inst_learning_loop_flag               true
% 3.70/0.99  --inst_learning_start                   3000
% 3.70/0.99  --inst_learning_factor                  2
% 3.70/0.99  --inst_start_prop_sim_after_learn       3
% 3.70/0.99  --inst_sel_renew                        solver
% 3.70/0.99  --inst_lit_activity_flag                true
% 3.70/0.99  --inst_restr_to_given                   false
% 3.70/0.99  --inst_activity_threshold               500
% 3.70/0.99  --inst_out_proof                        true
% 3.70/0.99  
% 3.70/0.99  ------ Resolution Options
% 3.70/0.99  
% 3.70/0.99  --resolution_flag                       false
% 3.70/0.99  --res_lit_sel                           adaptive
% 3.70/0.99  --res_lit_sel_side                      none
% 3.70/0.99  --res_ordering                          kbo
% 3.70/0.99  --res_to_prop_solver                    active
% 3.70/0.99  --res_prop_simpl_new                    false
% 3.70/0.99  --res_prop_simpl_given                  true
% 3.70/0.99  --res_passive_queue_type                priority_queues
% 3.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     false
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   []
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_full_bw                           [BwDemod]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS status Theorem for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  fof(f11,conjecture,(
% 3.70/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f12,negated_conjecture,(
% 3.70/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.70/0.99    inference(negated_conjecture,[],[f11])).
% 3.70/0.99  
% 3.70/0.99  fof(f29,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f12])).
% 3.70/0.99  
% 3.70/0.99  fof(f30,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.70/0.99    inference(flattening,[],[f29])).
% 3.70/0.99  
% 3.70/0.99  fof(f43,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f42,plain,(
% 3.70/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f41,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f40,plain,(
% 3.70/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f39,plain,(
% 3.70/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f38,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f44,plain,(
% 3.70/0.99    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f30,f43,f42,f41,f40,f39,f38])).
% 3.70/0.99  
% 3.70/0.99  fof(f73,plain,(
% 3.70/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f8,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f23,plain,(
% 3.70/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.70/0.99    inference(ennf_transformation,[],[f8])).
% 3.70/0.99  
% 3.70/0.99  fof(f24,plain,(
% 3.70/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.70/0.99    inference(flattening,[],[f23])).
% 3.70/0.99  
% 3.70/0.99  fof(f57,plain,(
% 3.70/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f24])).
% 3.70/0.99  
% 3.70/0.99  fof(f71,plain,(
% 3.70/0.99    v1_funct_1(sK6)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f76,plain,(
% 3.70/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f74,plain,(
% 3.70/0.99    v1_funct_1(sK7)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f69,plain,(
% 3.70/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f4,axiom,(
% 3.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f18,plain,(
% 3.70/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f4])).
% 3.70/0.99  
% 3.70/0.99  fof(f52,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f18])).
% 3.70/0.99  
% 3.70/0.99  fof(f9,axiom,(
% 3.70/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f25,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f9])).
% 3.70/0.99  
% 3.70/0.99  fof(f26,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/0.99    inference(flattening,[],[f25])).
% 3.70/0.99  
% 3.70/0.99  fof(f36,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f26])).
% 3.70/0.99  
% 3.70/0.99  fof(f37,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/0.99    inference(flattening,[],[f36])).
% 3.70/0.99  
% 3.70/0.99  fof(f58,plain,(
% 3.70/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f37])).
% 3.70/0.99  
% 3.70/0.99  fof(f82,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(equality_resolution,[],[f58])).
% 3.70/0.99  
% 3.70/0.99  fof(f10,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f27,plain,(
% 3.70/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f10])).
% 3.70/0.99  
% 3.70/0.99  fof(f28,plain,(
% 3.70/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.70/0.99    inference(flattening,[],[f27])).
% 3.70/0.99  
% 3.70/0.99  fof(f61,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f28])).
% 3.70/0.99  
% 3.70/0.99  fof(f62,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f28])).
% 3.70/0.99  
% 3.70/0.99  fof(f63,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f28])).
% 3.70/0.99  
% 3.70/0.99  fof(f64,plain,(
% 3.70/0.99    ~v1_xboole_0(sK2)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f68,plain,(
% 3.70/0.99    ~v1_xboole_0(sK5)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f65,plain,(
% 3.70/0.99    ~v1_xboole_0(sK3)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f75,plain,(
% 3.70/0.99    v1_funct_2(sK7,sK5,sK3)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f7,axiom,(
% 3.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f22,plain,(
% 3.70/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.99    inference(ennf_transformation,[],[f7])).
% 3.70/0.99  
% 3.70/0.99  fof(f56,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f22])).
% 3.70/0.99  
% 3.70/0.99  fof(f5,axiom,(
% 3.70/0.99    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f19,plain,(
% 3.70/0.99    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f5])).
% 3.70/0.99  
% 3.70/0.99  fof(f53,plain,(
% 3.70/0.99    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f19])).
% 3.70/0.99  
% 3.70/0.99  fof(f6,axiom,(
% 3.70/0.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f20,plain,(
% 3.70/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f6])).
% 3.70/0.99  
% 3.70/0.99  fof(f21,plain,(
% 3.70/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.70/0.99    inference(flattening,[],[f20])).
% 3.70/0.99  
% 3.70/0.99  fof(f35,plain,(
% 3.70/0.99    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f21])).
% 3.70/0.99  
% 3.70/0.99  fof(f54,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f35])).
% 3.70/0.99  
% 3.70/0.99  fof(f70,plain,(
% 3.70/0.99    r1_subset_1(sK4,sK5)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f66,plain,(
% 3.70/0.99    ~v1_xboole_0(sK4)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f1,axiom,(
% 3.70/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f13,plain,(
% 3.70/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.70/0.99    inference(rectify,[],[f1])).
% 3.70/0.99  
% 3.70/0.99  fof(f15,plain,(
% 3.70/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.70/0.99    inference(ennf_transformation,[],[f13])).
% 3.70/0.99  
% 3.70/0.99  fof(f31,plain,(
% 3.70/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f32,plain,(
% 3.70/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f31])).
% 3.70/0.99  
% 3.70/0.99  fof(f45,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f32])).
% 3.70/0.99  
% 3.70/0.99  fof(f2,axiom,(
% 3.70/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f14,plain,(
% 3.70/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.70/0.99    inference(rectify,[],[f2])).
% 3.70/0.99  
% 3.70/0.99  fof(f16,plain,(
% 3.70/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.70/0.99    inference(ennf_transformation,[],[f14])).
% 3.70/0.99  
% 3.70/0.99  fof(f33,plain,(
% 3.70/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f34,plain,(
% 3.70/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f33])).
% 3.70/0.99  
% 3.70/0.99  fof(f49,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f34])).
% 3.70/0.99  
% 3.70/0.99  fof(f3,axiom,(
% 3.70/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f17,plain,(
% 3.70/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f3])).
% 3.70/0.99  
% 3.70/0.99  fof(f51,plain,(
% 3.70/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 3.70/0.99    inference(cnf_transformation,[],[f17])).
% 3.70/0.99  
% 3.70/0.99  fof(f59,plain,(
% 3.70/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f37])).
% 3.70/0.99  
% 3.70/0.99  fof(f81,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(equality_resolution,[],[f59])).
% 3.70/0.99  
% 3.70/0.99  fof(f67,plain,(
% 3.70/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f72,plain,(
% 3.70/0.99    v1_funct_2(sK6,sK4,sK3)),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f77,plain,(
% 3.70/0.99    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  cnf(c_23,negated_conjecture,
% 3.70/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.70/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1458,plain,
% 3.70/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_12,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.70/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1466,plain,
% 3.70/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3729,plain,
% 3.70/0.99      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
% 3.70/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1458,c_1466]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_25,negated_conjecture,
% 3.70/0.99      ( v1_funct_1(sK6) ),
% 3.70/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1853,plain,
% 3.70/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.70/0.99      | ~ v1_funct_1(sK6)
% 3.70/0.99      | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2037,plain,
% 3.70/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.70/0.99      | ~ v1_funct_1(sK6)
% 3.70/0.99      | k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1853]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4088,plain,
% 3.70/0.99      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_3729,c_25,c_23,c_2037]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_20,negated_conjecture,
% 3.70/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 3.70/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1461,plain,
% 3.70/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3728,plain,
% 3.70/0.99      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
% 3.70/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1461,c_1466]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_22,negated_conjecture,
% 3.70/0.99      ( v1_funct_1(sK7) ),
% 3.70/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1848,plain,
% 3.70/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.70/0.99      | ~ v1_funct_1(sK7)
% 3.70/0.99      | k2_partfun1(X0,X1,sK7,X2) = k7_relat_1(sK7,X2) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2028,plain,
% 3.70/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 3.70/0.99      | ~ v1_funct_1(sK7)
% 3.70/0.99      | k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1848]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3876,plain,
% 3.70/0.99      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_3728,c_22,c_20,c_2028]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_27,negated_conjecture,
% 3.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1455,plain,
% 3.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_7,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.70/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1467,plain,
% 3.70/0.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2751,plain,
% 3.70/0.99      ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1455,c_1467]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_15,plain,
% 3.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_1(X3)
% 3.70/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X1)
% 3.70/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.70/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_18,plain,
% 3.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_1(X3)
% 3.70/0.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_17,plain,
% 3.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_1(X3)
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_16,plain,
% 3.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_1(X3)
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_178,plain,
% 3.70/0.99      ( ~ v1_funct_1(X3)
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X1)
% 3.70/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_15,c_18,c_17,c_16]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_179,plain,
% 3.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_1(X3)
% 3.70/0.99      | v1_xboole_0(X1)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_178]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1449,plain,
% 3.70/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.70/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_funct_1(X5) != iProver_top
% 3.70/0.99      | v1_xboole_0(X3) = iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X4) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_179]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3414,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
% 3.70/0.99      | k2_partfun1(sK5,X1,X3,k9_subset_1(sK2,X0,sK5)) != k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5))
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(X3) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_2751,c_1449]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3460,plain,
% 3.70/0.99      ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(X3) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_3414,c_2751]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_32,negated_conjecture,
% 3.70/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.70/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_33,plain,
% 3.70/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_28,negated_conjecture,
% 3.70/0.99      ( ~ v1_xboole_0(sK5) ),
% 3.70/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_37,plain,
% 3.70/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_38,plain,
% 3.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6468,plain,
% 3.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
% 3.70/0.99      | k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
% 3.70/0.99      | v1_funct_1(X3) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_3460,c_33,c_37,c_38]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6469,plain,
% 3.70/0.99      ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),X0) = X2
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(X3) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_6468]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6487,plain,
% 3.70/0.99      ( k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.70/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/0.99      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.70/0.99      | v1_funct_1(X1) != iProver_top
% 3.70/0.99      | v1_funct_1(sK7) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3876,c_6469]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_31,negated_conjecture,
% 3.70/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.70/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_34,plain,
% 3.70/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_43,plain,
% 3.70/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_21,negated_conjecture,
% 3.70/0.99      ( v1_funct_2(sK7,sK5,sK3) ),
% 3.70/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_44,plain,
% 3.70/0.99      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_45,plain,
% 3.70/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6750,plain,
% 3.70/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/0.99      | k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.70/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_6487,c_34,c_43,c_44,c_45]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6751,plain,
% 3.70/0.99      ( k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.70/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(X1) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_6750]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6764,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.70/0.99      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 3.70/0.99      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(sK6) != iProver_top
% 3.70/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4088,c_6751]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_11,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | v1_relat_1(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8,plain,
% 3.70/0.99      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_356,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.70/0.99      inference(resolution,[status(thm)],[c_11,c_8]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1447,plain,
% 3.70/0.99      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2313,plain,
% 3.70/0.99      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1461,c_1447]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2314,plain,
% 3.70/0.99      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1458,c_1447]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_10,plain,
% 3.70/0.99      ( ~ r1_subset_1(X0,X1)
% 3.70/0.99      | r1_xboole_0(X0,X1)
% 3.70/0.99      | v1_xboole_0(X0)
% 3.70/0.99      | v1_xboole_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_26,negated_conjecture,
% 3.70/0.99      ( r1_subset_1(sK4,sK5) ),
% 3.70/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_371,plain,
% 3.70/0.99      ( r1_xboole_0(X0,X1)
% 3.70/0.99      | v1_xboole_0(X0)
% 3.70/0.99      | v1_xboole_0(X1)
% 3.70/0.99      | sK5 != X1
% 3.70/0.99      | sK4 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_372,plain,
% 3.70/0.99      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_371]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_30,negated_conjecture,
% 3.70/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.70/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_374,plain,
% 3.70/0.99      ( r1_xboole_0(sK4,sK5) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_372,c_30,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1446,plain,
% 3.70/0.99      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2,plain,
% 3.70/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1472,plain,
% 3.70/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.70/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3,plain,
% 3.70/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.70/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1471,plain,
% 3.70/0.99      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.70/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2641,plain,
% 3.70/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.70/0.99      | r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1472,c_1471]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5,plain,
% 3.70/0.99      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1469,plain,
% 3.70/0.99      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5294,plain,
% 3.70/0.99      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.70/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_2641,c_1469]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5302,plain,
% 3.70/0.99      ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1446,c_5294]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6788,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.70/0.99      | k1_xboole_0 != k1_xboole_0
% 3.70/0.99      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(sK6) != iProver_top
% 3.70/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_6764,c_2313,c_2314,c_5302]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6789,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.70/0.99      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(sK6) != iProver_top
% 3.70/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/0.99      inference(equality_resolution_simp,[status(thm)],[c_6788]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14,plain,
% 3.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_1(X3)
% 3.70/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X1)
% 3.70/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_185,plain,
% 3.70/0.99      ( ~ v1_funct_1(X3)
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X1)
% 3.70/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_14,c_18,c_17,c_16]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_186,plain,
% 3.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.70/0.99      | ~ v1_funct_1(X0)
% 3.70/0.99      | ~ v1_funct_1(X3)
% 3.70/0.99      | v1_xboole_0(X1)
% 3.70/0.99      | v1_xboole_0(X2)
% 3.70/0.99      | v1_xboole_0(X4)
% 3.70/0.99      | v1_xboole_0(X5)
% 3.70/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.70/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_185]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1448,plain,
% 3.70/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.70/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_funct_1(X5) != iProver_top
% 3.70/0.99      | v1_xboole_0(X3) = iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X4) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2768,plain,
% 3.70/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(sK2,X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_funct_1(X3) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_2751,c_1448]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2783,plain,
% 3.70/0.99      ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(X3) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_2768,c_2751]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3246,plain,
% 3.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
% 3.70/0.99      | k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
% 3.70/0.99      | v1_funct_1(X3) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_2783,c_33,c_37,c_38]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3247,plain,
% 3.70/0.99      ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK5)) != k2_partfun1(sK5,X1,X3,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),X1,k1_tmap_1(sK2,X1,X0,sK5,X2,X3),sK5) = X3
% 3.70/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.99      | v1_funct_2(X3,sK5,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(X3) != iProver_top
% 3.70/0.99      | v1_funct_1(X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_3246]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3886,plain,
% 3.70/0.99      ( k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.70/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/0.99      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.70/0.99      | v1_funct_1(X1) != iProver_top
% 3.70/0.99      | v1_funct_1(sK7) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3876,c_3247]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4723,plain,
% 3.70/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/0.99      | k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.70/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_3886,c_34,c_43,c_44,c_45]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4724,plain,
% 3.70/0.99      ( k2_partfun1(X0,sK3,X1,k3_xboole_0(X0,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,X0,sK5),sK3,k1_tmap_1(sK2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.70/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(X1) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_4723]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4737,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.70/0.99      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 3.70/0.99      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.70/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.70/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 3.70/0.99      | v1_funct_1(sK6) != iProver_top
% 3.70/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4088,c_4724]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_29,negated_conjecture,
% 3.70/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_24,negated_conjecture,
% 3.70/0.99      ( v1_funct_2(sK6,sK4,sK3) ),
% 3.70/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4752,plain,
% 3.70/0.99      ( ~ v1_funct_2(sK6,sK4,sK3)
% 3.70/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.70/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 3.70/0.99      | ~ v1_funct_1(sK6)
% 3.70/0.99      | v1_xboole_0(sK4)
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.70/0.99      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 3.70/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4737]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4795,plain,
% 3.70/0.99      ( k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_4737,c_30,c_29,c_25,c_24,c_23,c_4752]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4796,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.70/0.99      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_4795]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5372,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.70/0.99      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_5302,c_4796]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5383,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.70/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_5372,c_2313,c_2314]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5384,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
% 3.70/0.99      inference(equality_resolution_simp,[status(thm)],[c_5383]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_19,negated_conjecture,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/0.99      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2766,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/0.99      | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_2751,c_19]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3880,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/0.99      | k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_3876,c_2766]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4307,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/0.99      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_3880,c_4088]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5373,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/0.99      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_5302,c_4307]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5377,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.70/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_5373,c_2313,c_2314]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5378,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.70/0.99      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 ),
% 3.70/0.99      inference(equality_resolution_simp,[status(thm)],[c_5377]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5386,plain,
% 3.70/0.99      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 ),
% 3.70/0.99      inference(backward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_5384,c_5378]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_42,plain,
% 3.70/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_41,plain,
% 3.70/0.99      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_40,plain,
% 3.70/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_36,plain,
% 3.70/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_35,plain,
% 3.70/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(contradiction,plain,
% 3.70/0.99      ( $false ),
% 3.70/0.99      inference(minisat,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_6789,c_5386,c_42,c_41,c_40,c_36,c_35]) ).
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  ------                               Statistics
% 3.70/0.99  
% 3.70/0.99  ------ General
% 3.70/0.99  
% 3.70/0.99  abstr_ref_over_cycles:                  0
% 3.70/0.99  abstr_ref_under_cycles:                 0
% 3.70/0.99  gc_basic_clause_elim:                   0
% 3.70/0.99  forced_gc_time:                         0
% 3.70/0.99  parsing_time:                           0.011
% 3.70/0.99  unif_index_cands_time:                  0.
% 3.70/0.99  unif_index_add_time:                    0.
% 3.70/0.99  orderings_time:                         0.
% 3.70/0.99  out_proof_time:                         0.015
% 3.70/0.99  total_time:                             0.337
% 3.70/0.99  num_of_symbols:                         56
% 3.70/0.99  num_of_terms:                           12695
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing
% 3.70/0.99  
% 3.70/0.99  num_of_splits:                          0
% 3.70/0.99  num_of_split_atoms:                     0
% 3.70/0.99  num_of_reused_defs:                     0
% 3.70/0.99  num_eq_ax_congr_red:                    22
% 3.70/0.99  num_of_sem_filtered_clauses:            1
% 3.70/0.99  num_of_subtypes:                        0
% 3.70/0.99  monotx_restored_types:                  0
% 3.70/0.99  sat_num_of_epr_types:                   0
% 3.70/0.99  sat_num_of_non_cyclic_types:            0
% 3.70/0.99  sat_guarded_non_collapsed_types:        0
% 3.70/0.99  num_pure_diseq_elim:                    0
% 3.70/0.99  simp_replaced_by:                       0
% 3.70/0.99  res_preprocessed:                       154
% 3.70/0.99  prep_upred:                             0
% 3.70/0.99  prep_unflattend:                        58
% 3.70/0.99  smt_new_axioms:                         0
% 3.70/0.99  pred_elim_cands:                        6
% 3.70/0.99  pred_elim:                              2
% 3.70/0.99  pred_elim_cl:                           3
% 3.70/0.99  pred_elim_cycles:                       4
% 3.70/0.99  merged_defs:                            0
% 3.70/0.99  merged_defs_ncl:                        0
% 3.70/0.99  bin_hyper_res:                          0
% 3.70/0.99  prep_cycles:                            4
% 3.70/0.99  pred_elim_time:                         0.006
% 3.70/0.99  splitting_time:                         0.
% 3.70/0.99  sem_filter_time:                        0.
% 3.70/0.99  monotx_time:                            0.001
% 3.70/0.99  subtype_inf_time:                       0.
% 3.70/0.99  
% 3.70/0.99  ------ Problem properties
% 3.70/0.99  
% 3.70/0.99  clauses:                                30
% 3.70/0.99  conjectures:                            13
% 3.70/0.99  epr:                                    12
% 3.70/0.99  horn:                                   21
% 3.70/0.99  ground:                                 15
% 3.70/0.99  unary:                                  14
% 3.70/0.99  binary:                                 7
% 3.70/0.99  lits:                                   121
% 3.70/0.99  lits_eq:                                13
% 3.70/0.99  fd_pure:                                0
% 3.70/0.99  fd_pseudo:                              0
% 3.70/0.99  fd_cond:                                1
% 3.70/0.99  fd_pseudo_cond:                         0
% 3.70/0.99  ac_symbols:                             0
% 3.70/0.99  
% 3.70/0.99  ------ Propositional Solver
% 3.70/0.99  
% 3.70/0.99  prop_solver_calls:                      26
% 3.70/0.99  prop_fast_solver_calls:                 1819
% 3.70/0.99  smt_solver_calls:                       0
% 3.70/0.99  smt_fast_solver_calls:                  0
% 3.70/0.99  prop_num_of_clauses:                    2543
% 3.70/0.99  prop_preprocess_simplified:             6478
% 3.70/0.99  prop_fo_subsumed:                       103
% 3.70/0.99  prop_solver_time:                       0.
% 3.70/0.99  smt_solver_time:                        0.
% 3.70/0.99  smt_fast_solver_time:                   0.
% 3.70/0.99  prop_fast_solver_time:                  0.
% 3.70/0.99  prop_unsat_core_time:                   0.
% 3.70/0.99  
% 3.70/0.99  ------ QBF
% 3.70/0.99  
% 3.70/0.99  qbf_q_res:                              0
% 3.70/0.99  qbf_num_tautologies:                    0
% 3.70/0.99  qbf_prep_cycles:                        0
% 3.70/0.99  
% 3.70/0.99  ------ BMC1
% 3.70/0.99  
% 3.70/0.99  bmc1_current_bound:                     -1
% 3.70/0.99  bmc1_last_solved_bound:                 -1
% 3.70/0.99  bmc1_unsat_core_size:                   -1
% 3.70/0.99  bmc1_unsat_core_parents_size:           -1
% 3.70/0.99  bmc1_merge_next_fun:                    0
% 3.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation
% 3.70/0.99  
% 3.70/0.99  inst_num_of_clauses:                    613
% 3.70/0.99  inst_num_in_passive:                    77
% 3.70/0.99  inst_num_in_active:                     330
% 3.70/0.99  inst_num_in_unprocessed:                206
% 3.70/0.99  inst_num_of_loops:                      360
% 3.70/0.99  inst_num_of_learning_restarts:          0
% 3.70/0.99  inst_num_moves_active_passive:          27
% 3.70/0.99  inst_lit_activity:                      0
% 3.70/0.99  inst_lit_activity_moves:                0
% 3.70/0.99  inst_num_tautologies:                   0
% 3.70/0.99  inst_num_prop_implied:                  0
% 3.70/0.99  inst_num_existing_simplified:           0
% 3.70/0.99  inst_num_eq_res_simplified:             0
% 3.70/0.99  inst_num_child_elim:                    0
% 3.70/0.99  inst_num_of_dismatching_blockings:      24
% 3.70/0.99  inst_num_of_non_proper_insts:           449
% 3.70/0.99  inst_num_of_duplicates:                 0
% 3.70/0.99  inst_inst_num_from_inst_to_res:         0
% 3.70/0.99  inst_dismatching_checking_time:         0.
% 3.70/0.99  
% 3.70/0.99  ------ Resolution
% 3.70/0.99  
% 3.70/0.99  res_num_of_clauses:                     0
% 3.70/0.99  res_num_in_passive:                     0
% 3.70/0.99  res_num_in_active:                      0
% 3.70/0.99  res_num_of_loops:                       158
% 3.70/0.99  res_forward_subset_subsumed:            16
% 3.70/0.99  res_backward_subset_subsumed:           0
% 3.70/0.99  res_forward_subsumed:                   0
% 3.70/0.99  res_backward_subsumed:                  0
% 3.70/0.99  res_forward_subsumption_resolution:     0
% 3.70/0.99  res_backward_subsumption_resolution:    0
% 3.70/0.99  res_clause_to_clause_subsumption:       346
% 3.70/0.99  res_orphan_elimination:                 0
% 3.70/0.99  res_tautology_del:                      20
% 3.70/0.99  res_num_eq_res_simplified:              0
% 3.70/0.99  res_num_sel_changes:                    0
% 3.70/0.99  res_moves_from_active_to_pass:          0
% 3.70/0.99  
% 3.70/0.99  ------ Superposition
% 3.70/0.99  
% 3.70/0.99  sup_time_total:                         0.
% 3.70/0.99  sup_time_generating:                    0.
% 3.70/0.99  sup_time_sim_full:                      0.
% 3.70/0.99  sup_time_sim_immed:                     0.
% 3.70/0.99  
% 3.70/0.99  sup_num_of_clauses:                     106
% 3.70/0.99  sup_num_in_active:                      67
% 3.70/0.99  sup_num_in_passive:                     39
% 3.70/0.99  sup_num_of_loops:                       70
% 3.70/0.99  sup_fw_superposition:                   61
% 3.70/0.99  sup_bw_superposition:                   41
% 3.70/0.99  sup_immediate_simplified:               43
% 3.70/0.99  sup_given_eliminated:                   0
% 3.70/0.99  comparisons_done:                       0
% 3.70/0.99  comparisons_avoided:                    0
% 3.70/0.99  
% 3.70/0.99  ------ Simplifications
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  sim_fw_subset_subsumed:                 9
% 3.70/0.99  sim_bw_subset_subsumed:                 2
% 3.70/0.99  sim_fw_subsumed:                        0
% 3.70/0.99  sim_bw_subsumed:                        0
% 3.70/0.99  sim_fw_subsumption_res:                 0
% 3.70/0.99  sim_bw_subsumption_res:                 1
% 3.70/0.99  sim_tautology_del:                      1
% 3.70/0.99  sim_eq_tautology_del:                   1
% 3.70/0.99  sim_eq_res_simp:                        3
% 3.70/0.99  sim_fw_demodulated:                     9
% 3.70/0.99  sim_bw_demodulated:                     4
% 3.70/0.99  sim_light_normalised:                   25
% 3.70/0.99  sim_joinable_taut:                      0
% 3.70/0.99  sim_joinable_simp:                      0
% 3.70/0.99  sim_ac_normalised:                      0
% 3.70/0.99  sim_smt_subsumption:                    0
% 3.70/0.99  
%------------------------------------------------------------------------------
