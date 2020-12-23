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
% DateTime   : Thu Dec  3 12:21:31 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  254 (4881 expanded)
%              Number of clauses        :  160 (1256 expanded)
%              Number of leaves         :   26 (1669 expanded)
%              Depth                    :   28
%              Number of atoms          : 1256 (52227 expanded)
%              Number of equality atoms :  439 (11785 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f60,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f45,f59,f58,f57,f56,f55,f54])).

fof(f96,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f102,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f80,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f78,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
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
    inference(equality_resolution,[],[f84])).

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

fof(f87,plain,(
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

fof(f88,plain,(
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

fof(f89,plain,(
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

fof(f98,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f90,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f103,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f60])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
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
    inference(equality_resolution,[],[f85])).

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

fof(f24,plain,(
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

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f46])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f48])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_15,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_518,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_519,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_521,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_40,c_38])).

cnf(c_1255,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_1926,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1269,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1912,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_21,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_429,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_17,c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_21,c_17,c_16])).

cnf(c_434,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_531,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_18,c_434])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_21,c_18,c_17,c_16])).

cnf(c_536,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_535])).

cnf(c_1254,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | v1_xboole_0(X2_57)
    | k1_relat_1(X0_57) = X1_57 ),
    inference(subtyping,[status(esa)],[c_536])).

cnf(c_1927,plain,
    ( k1_relat_1(X0_57) = X1_57
    | v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_10521,plain,
    ( k1_relat_1(sK7) = sK5
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1927])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2339,plain,
    ( ~ v1_funct_2(sK7,X0_57,X1_57)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(X1_57)
    | k1_relat_1(sK7) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_2518,plain,
    ( ~ v1_funct_2(sK7,sK5,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK3)
    | k1_relat_1(sK7) = sK5 ),
    inference(instantiation,[status(thm)],[c_2339])).

cnf(c_12005,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10521,c_41,c_32,c_31,c_30,c_2518])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1281,plain,
    ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1903,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1281])).

cnf(c_12035,plain,
    ( k7_relat_1(sK7,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_12005,c_1903])).

cnf(c_55,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1276,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2277,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_2278,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2277])).

cnf(c_12286,plain,
    ( r1_xboole_0(X0_57,sK5) != iProver_top
    | k7_relat_1(sK7,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12035,c_55,c_2278])).

cnf(c_12287,plain,
    ( k7_relat_1(sK7,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_12286])).

cnf(c_12294,plain,
    ( k7_relat_1(sK7,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1926,c_12287])).

cnf(c_1906,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1276])).

cnf(c_2817,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1906])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1277,plain,
    ( ~ v1_relat_1(X0_57)
    | k1_relat_1(k7_relat_1(X0_57,X1_57)) = k3_xboole_0(k1_relat_1(X0_57),X1_57) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1905,plain,
    ( k1_relat_1(k7_relat_1(X0_57,X1_57)) = k3_xboole_0(k1_relat_1(X0_57),X1_57)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1277])).

cnf(c_3693,plain,
    ( k1_relat_1(k7_relat_1(sK7,X0_57)) = k3_xboole_0(k1_relat_1(sK7),X0_57) ),
    inference(superposition,[status(thm)],[c_2817,c_1905])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1290,plain,
    ( k3_xboole_0(X0_57,X1_57) = k3_xboole_0(X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3945,plain,
    ( k1_relat_1(k7_relat_1(sK7,X0_57)) = k3_xboole_0(X0_57,k1_relat_1(sK7)) ),
    inference(superposition,[status(thm)],[c_3693,c_1290])).

cnf(c_12013,plain,
    ( k1_relat_1(k7_relat_1(sK7,X0_57)) = k3_xboole_0(X0_57,sK5) ),
    inference(demodulation,[status(thm)],[c_12005,c_3945])).

cnf(c_12768,plain,
    ( k3_xboole_0(sK4,sK5) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12294,c_12013])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1278,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_12770,plain,
    ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12768,c_1278])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1263,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_1918,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1263])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1282,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | k9_subset_1(X1_57,X2_57,X0_57) = k3_xboole_0(X2_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1902,plain,
    ( k9_subset_1(X0_57,X1_57,X2_57) = k3_xboole_0(X1_57,X2_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_2586,plain,
    ( k9_subset_1(sK2,X0_57,sK5) = k3_xboole_0(X0_57,sK5) ),
    inference(superposition,[status(thm)],[c_1918,c_1902])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1266,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1915,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1266])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1275,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1907,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_3612,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_1907])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2354,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0_57,X1_57,sK6,X2_57) = k7_relat_1(sK6,X2_57) ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_2529,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
    inference(instantiation,[status(thm)],[c_2354])).

cnf(c_3887,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3612,c_35,c_33,c_2529])).

cnf(c_3611,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1907])).

cnf(c_2349,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0_57,X1_57,sK7,X2_57) = k7_relat_1(sK7,X2_57) ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_2524,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
    inference(instantiation,[status(thm)],[c_2349])).

cnf(c_3806,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3611,c_32,c_30,c_2524])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f108])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f87])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f88])).

cnf(c_26,plain,
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
    inference(cnf_transformation,[],[f89])).

cnf(c_220,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_28,c_27,c_26])).

cnf(c_221,plain,
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
    inference(renaming,[status(thm)],[c_220])).

cnf(c_1257,plain,
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
    inference(subtyping,[status(esa)],[c_221])).

cnf(c_1924,plain,
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
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_7327,plain,
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
    inference(superposition,[status(thm)],[c_3806,c_1924])).

cnf(c_44,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_47,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_53,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_54,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8090,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
    | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7327,c_44,c_47,c_53,c_54,c_55])).

cnf(c_8091,plain,
    ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_8090])).

cnf(c_8106,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_8091])).

cnf(c_45,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_50,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_51,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_52,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8237,plain,
    ( v1_xboole_0(X0_57) = iProver_top
    | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8106,c_45,c_50,c_51,c_52])).

cnf(c_8238,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_8237])).

cnf(c_8248,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2586,c_8238])).

cnf(c_8249,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8248,c_2586])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_8250,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8249])).

cnf(c_8436,plain,
    ( k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8249,c_42,c_39,c_37,c_8250])).

cnf(c_8437,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_8436])).

cnf(c_13156,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_12770,c_8437])).

cnf(c_29,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1270,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2755,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_2586,c_1270])).

cnf(c_3810,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_3806,c_2755])).

cnf(c_3891,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_3810,c_3887])).

cnf(c_13157,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_12770,c_3891])).

cnf(c_13167,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_13156,c_13157])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_227,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_28,c_27,c_26])).

cnf(c_228,plain,
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
    inference(renaming,[status(thm)],[c_227])).

cnf(c_1256,plain,
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
    inference(subtyping,[status(esa)],[c_228])).

cnf(c_1925,plain,
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
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_8874,plain,
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
    inference(superposition,[status(thm)],[c_3806,c_1925])).

cnf(c_13981,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
    | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8874,c_44,c_47,c_53,c_54,c_55])).

cnf(c_13982,plain,
    ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
    | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_13981])).

cnf(c_13997,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_13982])).

cnf(c_14091,plain,
    ( v1_xboole_0(X0_57) = iProver_top
    | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13997,c_45,c_50,c_51,c_52])).

cnf(c_14092,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_14091])).

cnf(c_14102,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2586,c_14092])).

cnf(c_14103,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14102,c_12770])).

cnf(c_14104,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14103,c_2586])).

cnf(c_14105,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14104,c_12770])).

cnf(c_14106,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14105])).

cnf(c_20590,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13156,c_42,c_39,c_37,c_13167,c_14106])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1287,plain,
    ( r2_hidden(sK0(X0_57,X1_57),X0_57)
    | r1_xboole_0(X0_57,X1_57) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1898,plain,
    ( r2_hidden(sK0(X0_57,X1_57),X0_57) = iProver_top
    | r1_xboole_0(X0_57,X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1284,plain,
    ( k3_xboole_0(X0_57,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1286,plain,
    ( ~ r2_hidden(X0_59,k3_xboole_0(X0_57,X1_57))
    | ~ r1_xboole_0(X0_57,X1_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1899,plain,
    ( r2_hidden(X0_59,k3_xboole_0(X0_57,X1_57)) != iProver_top
    | r1_xboole_0(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1286])).

cnf(c_3483,plain,
    ( r2_hidden(X0_59,k1_xboole_0) != iProver_top
    | r1_xboole_0(X0_57,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1899])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1283,plain,
    ( r1_xboole_0(X0_57,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1343,plain,
    ( r1_xboole_0(X0_57,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1283])).

cnf(c_3536,plain,
    ( r2_hidden(X0_59,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3483,c_1343])).

cnf(c_3543,plain,
    ( r1_xboole_0(k1_xboole_0,X0_57) = iProver_top ),
    inference(superposition,[status(thm)],[c_1898,c_3536])).

cnf(c_12295,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3543,c_12287])).

cnf(c_10522,plain,
    ( k1_relat_1(sK6) = sK4
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_1927])).

cnf(c_2344,plain,
    ( ~ v1_funct_2(sK6,X0_57,X1_57)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X1_57)
    | k1_relat_1(sK6) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_2521,plain,
    ( ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK3)
    | k1_relat_1(sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_12040,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10522,c_41,c_35,c_34,c_33,c_2521])).

cnf(c_12066,plain,
    ( k7_relat_1(sK6,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12040,c_1903])).

cnf(c_2280,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_2281,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2280])).

cnf(c_12776,plain,
    ( r1_xboole_0(X0_57,sK4) != iProver_top
    | k7_relat_1(sK6,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12066,c_52,c_2281])).

cnf(c_12777,plain,
    ( k7_relat_1(sK6,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_12776])).

cnf(c_12784,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3543,c_12777])).

cnf(c_20592,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20590,c_12295,c_12784])).

cnf(c_20593,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_20592])).

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
% 0.12/0.33  % DateTime   : Tue Dec  1 09:32:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.49/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/1.48  
% 7.49/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.48  
% 7.49/1.48  ------  iProver source info
% 7.49/1.48  
% 7.49/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.48  git: non_committed_changes: false
% 7.49/1.48  git: last_make_outside_of_git: false
% 7.49/1.48  
% 7.49/1.48  ------ 
% 7.49/1.48  
% 7.49/1.48  ------ Input Options
% 7.49/1.48  
% 7.49/1.48  --out_options                           all
% 7.49/1.48  --tptp_safe_out                         true
% 7.49/1.48  --problem_path                          ""
% 7.49/1.48  --include_path                          ""
% 7.49/1.48  --clausifier                            res/vclausify_rel
% 7.49/1.48  --clausifier_options                    --mode clausify
% 7.49/1.48  --stdin                                 false
% 7.49/1.48  --stats_out                             all
% 7.49/1.48  
% 7.49/1.48  ------ General Options
% 7.49/1.48  
% 7.49/1.48  --fof                                   false
% 7.49/1.48  --time_out_real                         305.
% 7.49/1.48  --time_out_virtual                      -1.
% 7.49/1.48  --symbol_type_check                     false
% 7.49/1.48  --clausify_out                          false
% 7.49/1.48  --sig_cnt_out                           false
% 7.49/1.48  --trig_cnt_out                          false
% 7.49/1.48  --trig_cnt_out_tolerance                1.
% 7.49/1.48  --trig_cnt_out_sk_spl                   false
% 7.49/1.48  --abstr_cl_out                          false
% 7.49/1.48  
% 7.49/1.48  ------ Global Options
% 7.49/1.48  
% 7.49/1.48  --schedule                              default
% 7.49/1.48  --add_important_lit                     false
% 7.49/1.48  --prop_solver_per_cl                    1000
% 7.49/1.48  --min_unsat_core                        false
% 7.49/1.48  --soft_assumptions                      false
% 7.49/1.48  --soft_lemma_size                       3
% 7.49/1.48  --prop_impl_unit_size                   0
% 7.49/1.48  --prop_impl_unit                        []
% 7.49/1.48  --share_sel_clauses                     true
% 7.49/1.48  --reset_solvers                         false
% 7.49/1.48  --bc_imp_inh                            [conj_cone]
% 7.49/1.48  --conj_cone_tolerance                   3.
% 7.49/1.48  --extra_neg_conj                        none
% 7.49/1.48  --large_theory_mode                     true
% 7.49/1.48  --prolific_symb_bound                   200
% 7.49/1.48  --lt_threshold                          2000
% 7.49/1.48  --clause_weak_htbl                      true
% 7.49/1.48  --gc_record_bc_elim                     false
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing Options
% 7.49/1.48  
% 7.49/1.48  --preprocessing_flag                    true
% 7.49/1.48  --time_out_prep_mult                    0.1
% 7.49/1.48  --splitting_mode                        input
% 7.49/1.48  --splitting_grd                         true
% 7.49/1.48  --splitting_cvd                         false
% 7.49/1.48  --splitting_cvd_svl                     false
% 7.49/1.48  --splitting_nvd                         32
% 7.49/1.48  --sub_typing                            true
% 7.49/1.48  --prep_gs_sim                           true
% 7.49/1.48  --prep_unflatten                        true
% 7.49/1.48  --prep_res_sim                          true
% 7.49/1.48  --prep_upred                            true
% 7.49/1.48  --prep_sem_filter                       exhaustive
% 7.49/1.48  --prep_sem_filter_out                   false
% 7.49/1.48  --pred_elim                             true
% 7.49/1.48  --res_sim_input                         true
% 7.49/1.48  --eq_ax_congr_red                       true
% 7.49/1.48  --pure_diseq_elim                       true
% 7.49/1.48  --brand_transform                       false
% 7.49/1.48  --non_eq_to_eq                          false
% 7.49/1.48  --prep_def_merge                        true
% 7.49/1.48  --prep_def_merge_prop_impl              false
% 7.49/1.48  --prep_def_merge_mbd                    true
% 7.49/1.48  --prep_def_merge_tr_red                 false
% 7.49/1.48  --prep_def_merge_tr_cl                  false
% 7.49/1.48  --smt_preprocessing                     true
% 7.49/1.48  --smt_ac_axioms                         fast
% 7.49/1.48  --preprocessed_out                      false
% 7.49/1.48  --preprocessed_stats                    false
% 7.49/1.48  
% 7.49/1.48  ------ Abstraction refinement Options
% 7.49/1.48  
% 7.49/1.48  --abstr_ref                             []
% 7.49/1.48  --abstr_ref_prep                        false
% 7.49/1.48  --abstr_ref_until_sat                   false
% 7.49/1.48  --abstr_ref_sig_restrict                funpre
% 7.49/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.48  --abstr_ref_under                       []
% 7.49/1.48  
% 7.49/1.48  ------ SAT Options
% 7.49/1.48  
% 7.49/1.48  --sat_mode                              false
% 7.49/1.48  --sat_fm_restart_options                ""
% 7.49/1.48  --sat_gr_def                            false
% 7.49/1.48  --sat_epr_types                         true
% 7.49/1.48  --sat_non_cyclic_types                  false
% 7.49/1.48  --sat_finite_models                     false
% 7.49/1.48  --sat_fm_lemmas                         false
% 7.49/1.48  --sat_fm_prep                           false
% 7.49/1.48  --sat_fm_uc_incr                        true
% 7.49/1.48  --sat_out_model                         small
% 7.49/1.48  --sat_out_clauses                       false
% 7.49/1.48  
% 7.49/1.48  ------ QBF Options
% 7.49/1.48  
% 7.49/1.48  --qbf_mode                              false
% 7.49/1.48  --qbf_elim_univ                         false
% 7.49/1.48  --qbf_dom_inst                          none
% 7.49/1.48  --qbf_dom_pre_inst                      false
% 7.49/1.48  --qbf_sk_in                             false
% 7.49/1.48  --qbf_pred_elim                         true
% 7.49/1.48  --qbf_split                             512
% 7.49/1.48  
% 7.49/1.48  ------ BMC1 Options
% 7.49/1.48  
% 7.49/1.48  --bmc1_incremental                      false
% 7.49/1.48  --bmc1_axioms                           reachable_all
% 7.49/1.48  --bmc1_min_bound                        0
% 7.49/1.48  --bmc1_max_bound                        -1
% 7.49/1.48  --bmc1_max_bound_default                -1
% 7.49/1.48  --bmc1_symbol_reachability              true
% 7.49/1.48  --bmc1_property_lemmas                  false
% 7.49/1.48  --bmc1_k_induction                      false
% 7.49/1.48  --bmc1_non_equiv_states                 false
% 7.49/1.48  --bmc1_deadlock                         false
% 7.49/1.48  --bmc1_ucm                              false
% 7.49/1.48  --bmc1_add_unsat_core                   none
% 7.49/1.48  --bmc1_unsat_core_children              false
% 7.49/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.48  --bmc1_out_stat                         full
% 7.49/1.48  --bmc1_ground_init                      false
% 7.49/1.48  --bmc1_pre_inst_next_state              false
% 7.49/1.48  --bmc1_pre_inst_state                   false
% 7.49/1.48  --bmc1_pre_inst_reach_state             false
% 7.49/1.48  --bmc1_out_unsat_core                   false
% 7.49/1.48  --bmc1_aig_witness_out                  false
% 7.49/1.48  --bmc1_verbose                          false
% 7.49/1.48  --bmc1_dump_clauses_tptp                false
% 7.49/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.48  --bmc1_dump_file                        -
% 7.49/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.48  --bmc1_ucm_extend_mode                  1
% 7.49/1.48  --bmc1_ucm_init_mode                    2
% 7.49/1.48  --bmc1_ucm_cone_mode                    none
% 7.49/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.48  --bmc1_ucm_relax_model                  4
% 7.49/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.48  --bmc1_ucm_layered_model                none
% 7.49/1.48  --bmc1_ucm_max_lemma_size               10
% 7.49/1.48  
% 7.49/1.48  ------ AIG Options
% 7.49/1.48  
% 7.49/1.48  --aig_mode                              false
% 7.49/1.48  
% 7.49/1.48  ------ Instantiation Options
% 7.49/1.48  
% 7.49/1.48  --instantiation_flag                    true
% 7.49/1.48  --inst_sos_flag                         false
% 7.49/1.48  --inst_sos_phase                        true
% 7.49/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.48  --inst_lit_sel_side                     num_symb
% 7.49/1.48  --inst_solver_per_active                1400
% 7.49/1.48  --inst_solver_calls_frac                1.
% 7.49/1.48  --inst_passive_queue_type               priority_queues
% 7.49/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.48  --inst_passive_queues_freq              [25;2]
% 7.49/1.48  --inst_dismatching                      true
% 7.49/1.48  --inst_eager_unprocessed_to_passive     true
% 7.49/1.48  --inst_prop_sim_given                   true
% 7.49/1.48  --inst_prop_sim_new                     false
% 7.49/1.48  --inst_subs_new                         false
% 7.49/1.48  --inst_eq_res_simp                      false
% 7.49/1.48  --inst_subs_given                       false
% 7.49/1.48  --inst_orphan_elimination               true
% 7.49/1.48  --inst_learning_loop_flag               true
% 7.49/1.48  --inst_learning_start                   3000
% 7.49/1.48  --inst_learning_factor                  2
% 7.49/1.48  --inst_start_prop_sim_after_learn       3
% 7.49/1.48  --inst_sel_renew                        solver
% 7.49/1.48  --inst_lit_activity_flag                true
% 7.49/1.48  --inst_restr_to_given                   false
% 7.49/1.48  --inst_activity_threshold               500
% 7.49/1.48  --inst_out_proof                        true
% 7.49/1.48  
% 7.49/1.48  ------ Resolution Options
% 7.49/1.48  
% 7.49/1.48  --resolution_flag                       true
% 7.49/1.48  --res_lit_sel                           adaptive
% 7.49/1.48  --res_lit_sel_side                      none
% 7.49/1.48  --res_ordering                          kbo
% 7.49/1.48  --res_to_prop_solver                    active
% 7.49/1.48  --res_prop_simpl_new                    false
% 7.49/1.48  --res_prop_simpl_given                  true
% 7.49/1.48  --res_passive_queue_type                priority_queues
% 7.49/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.48  --res_passive_queues_freq               [15;5]
% 7.49/1.48  --res_forward_subs                      full
% 7.49/1.48  --res_backward_subs                     full
% 7.49/1.48  --res_forward_subs_resolution           true
% 7.49/1.48  --res_backward_subs_resolution          true
% 7.49/1.48  --res_orphan_elimination                true
% 7.49/1.48  --res_time_limit                        2.
% 7.49/1.48  --res_out_proof                         true
% 7.49/1.48  
% 7.49/1.48  ------ Superposition Options
% 7.49/1.48  
% 7.49/1.48  --superposition_flag                    true
% 7.49/1.48  --sup_passive_queue_type                priority_queues
% 7.49/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.48  --demod_completeness_check              fast
% 7.49/1.48  --demod_use_ground                      true
% 7.49/1.48  --sup_to_prop_solver                    passive
% 7.49/1.48  --sup_prop_simpl_new                    true
% 7.49/1.48  --sup_prop_simpl_given                  true
% 7.49/1.48  --sup_fun_splitting                     false
% 7.49/1.48  --sup_smt_interval                      50000
% 7.49/1.48  
% 7.49/1.48  ------ Superposition Simplification Setup
% 7.49/1.48  
% 7.49/1.48  --sup_indices_passive                   []
% 7.49/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_full_bw                           [BwDemod]
% 7.49/1.48  --sup_immed_triv                        [TrivRules]
% 7.49/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_immed_bw_main                     []
% 7.49/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.48  
% 7.49/1.48  ------ Combination Options
% 7.49/1.48  
% 7.49/1.48  --comb_res_mult                         3
% 7.49/1.48  --comb_sup_mult                         2
% 7.49/1.48  --comb_inst_mult                        10
% 7.49/1.48  
% 7.49/1.48  ------ Debug Options
% 7.49/1.48  
% 7.49/1.48  --dbg_backtrace                         false
% 7.49/1.48  --dbg_dump_prop_clauses                 false
% 7.49/1.48  --dbg_dump_prop_clauses_file            -
% 7.49/1.48  --dbg_out_stat                          false
% 7.49/1.48  ------ Parsing...
% 7.49/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.48  ------ Proving...
% 7.49/1.48  ------ Problem Properties 
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  clauses                                 37
% 7.49/1.48  conjectures                             13
% 7.49/1.48  EPR                                     11
% 7.49/1.48  Horn                                    27
% 7.49/1.48  unary                                   18
% 7.49/1.48  binary                                  8
% 7.49/1.48  lits                                    135
% 7.49/1.48  lits eq                                 19
% 7.49/1.48  fd_pure                                 0
% 7.49/1.48  fd_pseudo                               0
% 7.49/1.48  fd_cond                                 0
% 7.49/1.48  fd_pseudo_cond                          1
% 7.49/1.48  AC symbols                              0
% 7.49/1.48  
% 7.49/1.48  ------ Schedule dynamic 5 is on 
% 7.49/1.48  
% 7.49/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  ------ 
% 7.49/1.48  Current options:
% 7.49/1.48  ------ 
% 7.49/1.48  
% 7.49/1.48  ------ Input Options
% 7.49/1.48  
% 7.49/1.48  --out_options                           all
% 7.49/1.48  --tptp_safe_out                         true
% 7.49/1.48  --problem_path                          ""
% 7.49/1.48  --include_path                          ""
% 7.49/1.48  --clausifier                            res/vclausify_rel
% 7.49/1.48  --clausifier_options                    --mode clausify
% 7.49/1.48  --stdin                                 false
% 7.49/1.48  --stats_out                             all
% 7.49/1.48  
% 7.49/1.48  ------ General Options
% 7.49/1.48  
% 7.49/1.48  --fof                                   false
% 7.49/1.48  --time_out_real                         305.
% 7.49/1.48  --time_out_virtual                      -1.
% 7.49/1.48  --symbol_type_check                     false
% 7.49/1.48  --clausify_out                          false
% 7.49/1.48  --sig_cnt_out                           false
% 7.49/1.48  --trig_cnt_out                          false
% 7.49/1.48  --trig_cnt_out_tolerance                1.
% 7.49/1.48  --trig_cnt_out_sk_spl                   false
% 7.49/1.48  --abstr_cl_out                          false
% 7.49/1.48  
% 7.49/1.48  ------ Global Options
% 7.49/1.48  
% 7.49/1.48  --schedule                              default
% 7.49/1.48  --add_important_lit                     false
% 7.49/1.48  --prop_solver_per_cl                    1000
% 7.49/1.48  --min_unsat_core                        false
% 7.49/1.48  --soft_assumptions                      false
% 7.49/1.48  --soft_lemma_size                       3
% 7.49/1.48  --prop_impl_unit_size                   0
% 7.49/1.48  --prop_impl_unit                        []
% 7.49/1.48  --share_sel_clauses                     true
% 7.49/1.48  --reset_solvers                         false
% 7.49/1.48  --bc_imp_inh                            [conj_cone]
% 7.49/1.48  --conj_cone_tolerance                   3.
% 7.49/1.48  --extra_neg_conj                        none
% 7.49/1.48  --large_theory_mode                     true
% 7.49/1.48  --prolific_symb_bound                   200
% 7.49/1.48  --lt_threshold                          2000
% 7.49/1.48  --clause_weak_htbl                      true
% 7.49/1.48  --gc_record_bc_elim                     false
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing Options
% 7.49/1.48  
% 7.49/1.48  --preprocessing_flag                    true
% 7.49/1.48  --time_out_prep_mult                    0.1
% 7.49/1.48  --splitting_mode                        input
% 7.49/1.48  --splitting_grd                         true
% 7.49/1.48  --splitting_cvd                         false
% 7.49/1.48  --splitting_cvd_svl                     false
% 7.49/1.48  --splitting_nvd                         32
% 7.49/1.48  --sub_typing                            true
% 7.49/1.48  --prep_gs_sim                           true
% 7.49/1.48  --prep_unflatten                        true
% 7.49/1.48  --prep_res_sim                          true
% 7.49/1.48  --prep_upred                            true
% 7.49/1.48  --prep_sem_filter                       exhaustive
% 7.49/1.48  --prep_sem_filter_out                   false
% 7.49/1.48  --pred_elim                             true
% 7.49/1.48  --res_sim_input                         true
% 7.49/1.48  --eq_ax_congr_red                       true
% 7.49/1.48  --pure_diseq_elim                       true
% 7.49/1.48  --brand_transform                       false
% 7.49/1.48  --non_eq_to_eq                          false
% 7.49/1.48  --prep_def_merge                        true
% 7.49/1.48  --prep_def_merge_prop_impl              false
% 7.49/1.48  --prep_def_merge_mbd                    true
% 7.49/1.48  --prep_def_merge_tr_red                 false
% 7.49/1.48  --prep_def_merge_tr_cl                  false
% 7.49/1.48  --smt_preprocessing                     true
% 7.49/1.48  --smt_ac_axioms                         fast
% 7.49/1.48  --preprocessed_out                      false
% 7.49/1.48  --preprocessed_stats                    false
% 7.49/1.48  
% 7.49/1.48  ------ Abstraction refinement Options
% 7.49/1.48  
% 7.49/1.48  --abstr_ref                             []
% 7.49/1.48  --abstr_ref_prep                        false
% 7.49/1.48  --abstr_ref_until_sat                   false
% 7.49/1.48  --abstr_ref_sig_restrict                funpre
% 7.49/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.48  --abstr_ref_under                       []
% 7.49/1.48  
% 7.49/1.48  ------ SAT Options
% 7.49/1.48  
% 7.49/1.48  --sat_mode                              false
% 7.49/1.48  --sat_fm_restart_options                ""
% 7.49/1.48  --sat_gr_def                            false
% 7.49/1.48  --sat_epr_types                         true
% 7.49/1.48  --sat_non_cyclic_types                  false
% 7.49/1.48  --sat_finite_models                     false
% 7.49/1.48  --sat_fm_lemmas                         false
% 7.49/1.48  --sat_fm_prep                           false
% 7.49/1.48  --sat_fm_uc_incr                        true
% 7.49/1.48  --sat_out_model                         small
% 7.49/1.48  --sat_out_clauses                       false
% 7.49/1.48  
% 7.49/1.48  ------ QBF Options
% 7.49/1.48  
% 7.49/1.48  --qbf_mode                              false
% 7.49/1.48  --qbf_elim_univ                         false
% 7.49/1.48  --qbf_dom_inst                          none
% 7.49/1.48  --qbf_dom_pre_inst                      false
% 7.49/1.48  --qbf_sk_in                             false
% 7.49/1.48  --qbf_pred_elim                         true
% 7.49/1.48  --qbf_split                             512
% 7.49/1.48  
% 7.49/1.48  ------ BMC1 Options
% 7.49/1.48  
% 7.49/1.48  --bmc1_incremental                      false
% 7.49/1.48  --bmc1_axioms                           reachable_all
% 7.49/1.48  --bmc1_min_bound                        0
% 7.49/1.48  --bmc1_max_bound                        -1
% 7.49/1.48  --bmc1_max_bound_default                -1
% 7.49/1.48  --bmc1_symbol_reachability              true
% 7.49/1.48  --bmc1_property_lemmas                  false
% 7.49/1.48  --bmc1_k_induction                      false
% 7.49/1.48  --bmc1_non_equiv_states                 false
% 7.49/1.48  --bmc1_deadlock                         false
% 7.49/1.48  --bmc1_ucm                              false
% 7.49/1.48  --bmc1_add_unsat_core                   none
% 7.49/1.48  --bmc1_unsat_core_children              false
% 7.49/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.48  --bmc1_out_stat                         full
% 7.49/1.48  --bmc1_ground_init                      false
% 7.49/1.48  --bmc1_pre_inst_next_state              false
% 7.49/1.48  --bmc1_pre_inst_state                   false
% 7.49/1.48  --bmc1_pre_inst_reach_state             false
% 7.49/1.48  --bmc1_out_unsat_core                   false
% 7.49/1.48  --bmc1_aig_witness_out                  false
% 7.49/1.48  --bmc1_verbose                          false
% 7.49/1.48  --bmc1_dump_clauses_tptp                false
% 7.49/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.48  --bmc1_dump_file                        -
% 7.49/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.48  --bmc1_ucm_extend_mode                  1
% 7.49/1.48  --bmc1_ucm_init_mode                    2
% 7.49/1.48  --bmc1_ucm_cone_mode                    none
% 7.49/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.48  --bmc1_ucm_relax_model                  4
% 7.49/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.48  --bmc1_ucm_layered_model                none
% 7.49/1.48  --bmc1_ucm_max_lemma_size               10
% 7.49/1.48  
% 7.49/1.48  ------ AIG Options
% 7.49/1.48  
% 7.49/1.48  --aig_mode                              false
% 7.49/1.48  
% 7.49/1.48  ------ Instantiation Options
% 7.49/1.48  
% 7.49/1.48  --instantiation_flag                    true
% 7.49/1.48  --inst_sos_flag                         false
% 7.49/1.48  --inst_sos_phase                        true
% 7.49/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.48  --inst_lit_sel_side                     none
% 7.49/1.48  --inst_solver_per_active                1400
% 7.49/1.48  --inst_solver_calls_frac                1.
% 7.49/1.48  --inst_passive_queue_type               priority_queues
% 7.49/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.48  --inst_passive_queues_freq              [25;2]
% 7.49/1.48  --inst_dismatching                      true
% 7.49/1.48  --inst_eager_unprocessed_to_passive     true
% 7.49/1.48  --inst_prop_sim_given                   true
% 7.49/1.48  --inst_prop_sim_new                     false
% 7.49/1.48  --inst_subs_new                         false
% 7.49/1.48  --inst_eq_res_simp                      false
% 7.49/1.48  --inst_subs_given                       false
% 7.49/1.48  --inst_orphan_elimination               true
% 7.49/1.48  --inst_learning_loop_flag               true
% 7.49/1.48  --inst_learning_start                   3000
% 7.49/1.48  --inst_learning_factor                  2
% 7.49/1.48  --inst_start_prop_sim_after_learn       3
% 7.49/1.48  --inst_sel_renew                        solver
% 7.49/1.48  --inst_lit_activity_flag                true
% 7.49/1.48  --inst_restr_to_given                   false
% 7.49/1.48  --inst_activity_threshold               500
% 7.49/1.48  --inst_out_proof                        true
% 7.49/1.48  
% 7.49/1.48  ------ Resolution Options
% 7.49/1.48  
% 7.49/1.48  --resolution_flag                       false
% 7.49/1.48  --res_lit_sel                           adaptive
% 7.49/1.48  --res_lit_sel_side                      none
% 7.49/1.48  --res_ordering                          kbo
% 7.49/1.48  --res_to_prop_solver                    active
% 7.49/1.48  --res_prop_simpl_new                    false
% 7.49/1.48  --res_prop_simpl_given                  true
% 7.49/1.48  --res_passive_queue_type                priority_queues
% 7.49/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.48  --res_passive_queues_freq               [15;5]
% 7.49/1.48  --res_forward_subs                      full
% 7.49/1.48  --res_backward_subs                     full
% 7.49/1.48  --res_forward_subs_resolution           true
% 7.49/1.48  --res_backward_subs_resolution          true
% 7.49/1.48  --res_orphan_elimination                true
% 7.49/1.48  --res_time_limit                        2.
% 7.49/1.48  --res_out_proof                         true
% 7.49/1.48  
% 7.49/1.48  ------ Superposition Options
% 7.49/1.48  
% 7.49/1.48  --superposition_flag                    true
% 7.49/1.48  --sup_passive_queue_type                priority_queues
% 7.49/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.48  --demod_completeness_check              fast
% 7.49/1.48  --demod_use_ground                      true
% 7.49/1.48  --sup_to_prop_solver                    passive
% 7.49/1.48  --sup_prop_simpl_new                    true
% 7.49/1.48  --sup_prop_simpl_given                  true
% 7.49/1.48  --sup_fun_splitting                     false
% 7.49/1.48  --sup_smt_interval                      50000
% 7.49/1.48  
% 7.49/1.48  ------ Superposition Simplification Setup
% 7.49/1.48  
% 7.49/1.48  --sup_indices_passive                   []
% 7.49/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_full_bw                           [BwDemod]
% 7.49/1.48  --sup_immed_triv                        [TrivRules]
% 7.49/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_immed_bw_main                     []
% 7.49/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.48  
% 7.49/1.48  ------ Combination Options
% 7.49/1.48  
% 7.49/1.48  --comb_res_mult                         3
% 7.49/1.48  --comb_sup_mult                         2
% 7.49/1.48  --comb_inst_mult                        10
% 7.49/1.48  
% 7.49/1.48  ------ Debug Options
% 7.49/1.48  
% 7.49/1.48  --dbg_backtrace                         false
% 7.49/1.48  --dbg_dump_prop_clauses                 false
% 7.49/1.48  --dbg_dump_prop_clauses_file            -
% 7.49/1.48  --dbg_out_stat                          false
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  ------ Proving...
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  % SZS status Theorem for theBenchmark.p
% 7.49/1.48  
% 7.49/1.48   Resolution empty clause
% 7.49/1.48  
% 7.49/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.48  
% 7.49/1.48  fof(f11,axiom,(
% 7.49/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f30,plain,(
% 7.49/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.49/1.48    inference(ennf_transformation,[],[f11])).
% 7.49/1.48  
% 7.49/1.48  fof(f31,plain,(
% 7.49/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.49/1.48    inference(flattening,[],[f30])).
% 7.49/1.48  
% 7.49/1.48  fof(f50,plain,(
% 7.49/1.48    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.49/1.48    inference(nnf_transformation,[],[f31])).
% 7.49/1.48  
% 7.49/1.48  fof(f75,plain,(
% 7.49/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f50])).
% 7.49/1.48  
% 7.49/1.48  fof(f19,conjecture,(
% 7.49/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f20,negated_conjecture,(
% 7.49/1.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.49/1.48    inference(negated_conjecture,[],[f19])).
% 7.49/1.48  
% 7.49/1.48  fof(f44,plain,(
% 7.49/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.49/1.48    inference(ennf_transformation,[],[f20])).
% 7.49/1.48  
% 7.49/1.48  fof(f45,plain,(
% 7.49/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.49/1.48    inference(flattening,[],[f44])).
% 7.49/1.48  
% 7.49/1.48  fof(f59,plain,(
% 7.49/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f58,plain,(
% 7.49/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f57,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f56,plain,(
% 7.49/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f55,plain,(
% 7.49/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f54,plain,(
% 7.49/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f60,plain,(
% 7.49/1.48    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.49/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f45,f59,f58,f57,f56,f55,f54])).
% 7.49/1.48  
% 7.49/1.48  fof(f96,plain,(
% 7.49/1.48    r1_subset_1(sK4,sK5)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f92,plain,(
% 7.49/1.48    ~v1_xboole_0(sK4)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f94,plain,(
% 7.49/1.48    ~v1_xboole_0(sK5)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f102,plain,(
% 7.49/1.48    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f14,axiom,(
% 7.49/1.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f34,plain,(
% 7.49/1.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.49/1.48    inference(ennf_transformation,[],[f14])).
% 7.49/1.48  
% 7.49/1.48  fof(f35,plain,(
% 7.49/1.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.49/1.48    inference(flattening,[],[f34])).
% 7.49/1.48  
% 7.49/1.48  fof(f80,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f35])).
% 7.49/1.48  
% 7.49/1.48  fof(f13,axiom,(
% 7.49/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f23,plain,(
% 7.49/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.49/1.48    inference(pure_predicate_removal,[],[f13])).
% 7.49/1.48  
% 7.49/1.48  fof(f33,plain,(
% 7.49/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.48    inference(ennf_transformation,[],[f23])).
% 7.49/1.48  
% 7.49/1.48  fof(f78,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f33])).
% 7.49/1.48  
% 7.49/1.48  fof(f15,axiom,(
% 7.49/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f36,plain,(
% 7.49/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.49/1.48    inference(ennf_transformation,[],[f15])).
% 7.49/1.48  
% 7.49/1.48  fof(f37,plain,(
% 7.49/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(flattening,[],[f36])).
% 7.49/1.48  
% 7.49/1.48  fof(f51,plain,(
% 7.49/1.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(nnf_transformation,[],[f37])).
% 7.49/1.48  
% 7.49/1.48  fof(f81,plain,(
% 7.49/1.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f51])).
% 7.49/1.48  
% 7.49/1.48  fof(f12,axiom,(
% 7.49/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f32,plain,(
% 7.49/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.48    inference(ennf_transformation,[],[f12])).
% 7.49/1.48  
% 7.49/1.48  fof(f77,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f32])).
% 7.49/1.48  
% 7.49/1.48  fof(f91,plain,(
% 7.49/1.48    ~v1_xboole_0(sK3)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f100,plain,(
% 7.49/1.48    v1_funct_1(sK7)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f101,plain,(
% 7.49/1.48    v1_funct_2(sK7,sK5,sK3)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f7,axiom,(
% 7.49/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f27,plain,(
% 7.49/1.48    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.49/1.48    inference(ennf_transformation,[],[f7])).
% 7.49/1.48  
% 7.49/1.48  fof(f70,plain,(
% 7.49/1.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f27])).
% 7.49/1.48  
% 7.49/1.48  fof(f10,axiom,(
% 7.49/1.48    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f29,plain,(
% 7.49/1.48    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(ennf_transformation,[],[f10])).
% 7.49/1.48  
% 7.49/1.48  fof(f74,plain,(
% 7.49/1.48    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f29])).
% 7.49/1.48  
% 7.49/1.48  fof(f1,axiom,(
% 7.49/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f61,plain,(
% 7.49/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f1])).
% 7.49/1.48  
% 7.49/1.48  fof(f9,axiom,(
% 7.49/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f72,plain,(
% 7.49/1.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.49/1.48    inference(cnf_transformation,[],[f9])).
% 7.49/1.48  
% 7.49/1.48  fof(f95,plain,(
% 7.49/1.48    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f6,axiom,(
% 7.49/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f26,plain,(
% 7.49/1.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.49/1.48    inference(ennf_transformation,[],[f6])).
% 7.49/1.48  
% 7.49/1.48  fof(f69,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f26])).
% 7.49/1.48  
% 7.49/1.48  fof(f99,plain,(
% 7.49/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f16,axiom,(
% 7.49/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f38,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.49/1.48    inference(ennf_transformation,[],[f16])).
% 7.49/1.48  
% 7.49/1.48  fof(f39,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.49/1.48    inference(flattening,[],[f38])).
% 7.49/1.48  
% 7.49/1.48  fof(f83,plain,(
% 7.49/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f39])).
% 7.49/1.48  
% 7.49/1.48  fof(f97,plain,(
% 7.49/1.48    v1_funct_1(sK6)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f17,axiom,(
% 7.49/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f40,plain,(
% 7.49/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.49/1.48    inference(ennf_transformation,[],[f17])).
% 7.49/1.48  
% 7.49/1.48  fof(f41,plain,(
% 7.49/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.49/1.48    inference(flattening,[],[f40])).
% 7.49/1.48  
% 7.49/1.48  fof(f52,plain,(
% 7.49/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.49/1.48    inference(nnf_transformation,[],[f41])).
% 7.49/1.48  
% 7.49/1.48  fof(f53,plain,(
% 7.49/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.49/1.48    inference(flattening,[],[f52])).
% 7.49/1.48  
% 7.49/1.48  fof(f84,plain,(
% 7.49/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f53])).
% 7.49/1.48  
% 7.49/1.48  fof(f108,plain,(
% 7.49/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.48    inference(equality_resolution,[],[f84])).
% 7.49/1.48  
% 7.49/1.48  fof(f18,axiom,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f42,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.49/1.48    inference(ennf_transformation,[],[f18])).
% 7.49/1.48  
% 7.49/1.48  fof(f43,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.49/1.48    inference(flattening,[],[f42])).
% 7.49/1.48  
% 7.49/1.48  fof(f87,plain,(
% 7.49/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f43])).
% 7.49/1.48  
% 7.49/1.48  fof(f88,plain,(
% 7.49/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f43])).
% 7.49/1.48  
% 7.49/1.48  fof(f89,plain,(
% 7.49/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f43])).
% 7.49/1.48  
% 7.49/1.48  fof(f98,plain,(
% 7.49/1.48    v1_funct_2(sK6,sK4,sK3)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f90,plain,(
% 7.49/1.48    ~v1_xboole_0(sK2)),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f93,plain,(
% 7.49/1.48    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f103,plain,(
% 7.49/1.48    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 7.49/1.48    inference(cnf_transformation,[],[f60])).
% 7.49/1.48  
% 7.49/1.48  fof(f85,plain,(
% 7.49/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f53])).
% 7.49/1.48  
% 7.49/1.48  fof(f107,plain,(
% 7.49/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.48    inference(equality_resolution,[],[f85])).
% 7.49/1.48  
% 7.49/1.48  fof(f2,axiom,(
% 7.49/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f21,plain,(
% 7.49/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.49/1.48    inference(rectify,[],[f2])).
% 7.49/1.48  
% 7.49/1.48  fof(f24,plain,(
% 7.49/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.49/1.48    inference(ennf_transformation,[],[f21])).
% 7.49/1.48  
% 7.49/1.48  fof(f46,plain,(
% 7.49/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f47,plain,(
% 7.49/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.49/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f46])).
% 7.49/1.48  
% 7.49/1.48  fof(f62,plain,(
% 7.49/1.48    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f47])).
% 7.49/1.48  
% 7.49/1.48  fof(f4,axiom,(
% 7.49/1.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f67,plain,(
% 7.49/1.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.49/1.48    inference(cnf_transformation,[],[f4])).
% 7.49/1.48  
% 7.49/1.48  fof(f3,axiom,(
% 7.49/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f22,plain,(
% 7.49/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.49/1.48    inference(rectify,[],[f3])).
% 7.49/1.48  
% 7.49/1.48  fof(f25,plain,(
% 7.49/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.49/1.48    inference(ennf_transformation,[],[f22])).
% 7.49/1.48  
% 7.49/1.48  fof(f48,plain,(
% 7.49/1.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f49,plain,(
% 7.49/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.49/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f48])).
% 7.49/1.48  
% 7.49/1.48  fof(f66,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f49])).
% 7.49/1.48  
% 7.49/1.48  fof(f5,axiom,(
% 7.49/1.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f68,plain,(
% 7.49/1.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f5])).
% 7.49/1.49  
% 7.49/1.49  cnf(c_15,plain,
% 7.49/1.49      ( ~ r1_subset_1(X0,X1)
% 7.49/1.49      | r1_xboole_0(X0,X1)
% 7.49/1.49      | v1_xboole_0(X0)
% 7.49/1.49      | v1_xboole_0(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_36,negated_conjecture,
% 7.49/1.49      ( r1_subset_1(sK4,sK5) ),
% 7.49/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_518,plain,
% 7.49/1.49      ( r1_xboole_0(X0,X1)
% 7.49/1.49      | v1_xboole_0(X0)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | sK5 != X1
% 7.49/1.49      | sK4 != X0 ),
% 7.49/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_519,plain,
% 7.49/1.49      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 7.49/1.49      inference(unflattening,[status(thm)],[c_518]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_40,negated_conjecture,
% 7.49/1.49      ( ~ v1_xboole_0(sK4) ),
% 7.49/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_38,negated_conjecture,
% 7.49/1.49      ( ~ v1_xboole_0(sK5) ),
% 7.49/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_521,plain,
% 7.49/1.49      ( r1_xboole_0(sK4,sK5) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_519,c_40,c_38]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1255,plain,
% 7.49/1.49      ( r1_xboole_0(sK4,sK5) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_521]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1926,plain,
% 7.49/1.49      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1255]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_30,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.49/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1269,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_30]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1912,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_18,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | v1_partfun1(X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_xboole_0(X2) ),
% 7.49/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17,plain,
% 7.49/1.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.49/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_21,plain,
% 7.49/1.49      ( ~ v1_partfun1(X0,X1)
% 7.49/1.49      | ~ v4_relat_1(X0,X1)
% 7.49/1.49      | ~ v1_relat_1(X0)
% 7.49/1.49      | k1_relat_1(X0) = X1 ),
% 7.49/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_429,plain,
% 7.49/1.49      ( ~ v1_partfun1(X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_relat_1(X0)
% 7.49/1.49      | k1_relat_1(X0) = X1 ),
% 7.49/1.49      inference(resolution,[status(thm)],[c_17,c_21]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_433,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_partfun1(X0,X1)
% 7.49/1.49      | k1_relat_1(X0) = X1 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_429,c_21,c_17,c_16]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_434,plain,
% 7.49/1.49      ( ~ v1_partfun1(X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | k1_relat_1(X0) = X1 ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_433]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_531,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | k1_relat_1(X0) = X1 ),
% 7.49/1.49      inference(resolution,[status(thm)],[c_18,c_434]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_535,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | k1_relat_1(X0) = X1 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_531,c_21,c_18,c_17,c_16]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_536,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | k1_relat_1(X0) = X1 ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_535]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1254,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.49/1.49      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.49/1.49      | ~ v1_funct_1(X0_57)
% 7.49/1.49      | v1_xboole_0(X2_57)
% 7.49/1.49      | k1_relat_1(X0_57) = X1_57 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_536]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1927,plain,
% 7.49/1.49      ( k1_relat_1(X0_57) = X1_57
% 7.49/1.49      | v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_57) != iProver_top
% 7.49/1.49      | v1_xboole_0(X2_57) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_10521,plain,
% 7.49/1.49      ( k1_relat_1(sK7) = sK5
% 7.49/1.49      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.49/1.49      | v1_funct_1(sK7) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1912,c_1927]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_41,negated_conjecture,
% 7.49/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_32,negated_conjecture,
% 7.49/1.49      ( v1_funct_1(sK7) ),
% 7.49/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_31,negated_conjecture,
% 7.49/1.49      ( v1_funct_2(sK7,sK5,sK3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2339,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK7,X0_57,X1_57)
% 7.49/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.49/1.49      | ~ v1_funct_1(sK7)
% 7.49/1.49      | v1_xboole_0(X1_57)
% 7.49/1.49      | k1_relat_1(sK7) = X0_57 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1254]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2518,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK7,sK5,sK3)
% 7.49/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.49/1.49      | ~ v1_funct_1(sK7)
% 7.49/1.49      | v1_xboole_0(sK3)
% 7.49/1.49      | k1_relat_1(sK7) = sK5 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2339]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12005,plain,
% 7.49/1.49      ( k1_relat_1(sK7) = sK5 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_10521,c_41,c_32,c_31,c_30,c_2518]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_9,plain,
% 7.49/1.49      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.49/1.49      | ~ v1_relat_1(X1)
% 7.49/1.49      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.49/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1281,plain,
% 7.49/1.49      ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
% 7.49/1.49      | ~ v1_relat_1(X1_57)
% 7.49/1.49      | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1903,plain,
% 7.49/1.49      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.49/1.49      | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
% 7.49/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1281]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12035,plain,
% 7.49/1.49      ( k7_relat_1(sK7,X0_57) = k1_xboole_0
% 7.49/1.49      | r1_xboole_0(X0_57,sK5) != iProver_top
% 7.49/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_12005,c_1903]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_55,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1276,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.49/1.49      | v1_relat_1(X0_57) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2277,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.49/1.49      | v1_relat_1(sK7) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1276]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2278,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.49/1.49      | v1_relat_1(sK7) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_2277]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12286,plain,
% 7.49/1.49      ( r1_xboole_0(X0_57,sK5) != iProver_top
% 7.49/1.49      | k7_relat_1(sK7,X0_57) = k1_xboole_0 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_12035,c_55,c_2278]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12287,plain,
% 7.49/1.49      ( k7_relat_1(sK7,X0_57) = k1_xboole_0
% 7.49/1.49      | r1_xboole_0(X0_57,sK5) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_12286]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12294,plain,
% 7.49/1.49      ( k7_relat_1(sK7,sK4) = k1_xboole_0 ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1926,c_12287]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1906,plain,
% 7.49/1.49      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.49/1.49      | v1_relat_1(X0_57) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1276]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2817,plain,
% 7.49/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1912,c_1906]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13,plain,
% 7.49/1.49      ( ~ v1_relat_1(X0)
% 7.49/1.49      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1277,plain,
% 7.49/1.49      ( ~ v1_relat_1(X0_57)
% 7.49/1.49      | k1_relat_1(k7_relat_1(X0_57,X1_57)) = k3_xboole_0(k1_relat_1(X0_57),X1_57) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1905,plain,
% 7.49/1.49      ( k1_relat_1(k7_relat_1(X0_57,X1_57)) = k3_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.49/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1277]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3693,plain,
% 7.49/1.49      ( k1_relat_1(k7_relat_1(sK7,X0_57)) = k3_xboole_0(k1_relat_1(sK7),X0_57) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2817,c_1905]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_0,plain,
% 7.49/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1290,plain,
% 7.49/1.49      ( k3_xboole_0(X0_57,X1_57) = k3_xboole_0(X1_57,X0_57) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3945,plain,
% 7.49/1.49      ( k1_relat_1(k7_relat_1(sK7,X0_57)) = k3_xboole_0(X0_57,k1_relat_1(sK7)) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3693,c_1290]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12013,plain,
% 7.49/1.49      ( k1_relat_1(k7_relat_1(sK7,X0_57)) = k3_xboole_0(X0_57,sK5) ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_12005,c_3945]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12768,plain,
% 7.49/1.49      ( k3_xboole_0(sK4,sK5) = k1_relat_1(k1_xboole_0) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_12294,c_12013]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12,plain,
% 7.49/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.49/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1278,plain,
% 7.49/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12770,plain,
% 7.49/1.49      ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 7.49/1.49      inference(light_normalisation,[status(thm)],[c_12768,c_1278]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_37,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1263,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_37]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1918,plain,
% 7.49/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1263]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.49/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1282,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.49/1.49      | k9_subset_1(X1_57,X2_57,X0_57) = k3_xboole_0(X2_57,X0_57) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1902,plain,
% 7.49/1.49      ( k9_subset_1(X0_57,X1_57,X2_57) = k3_xboole_0(X1_57,X2_57)
% 7.49/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1282]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2586,plain,
% 7.49/1.49      ( k9_subset_1(sK2,X0_57,sK5) = k3_xboole_0(X0_57,sK5) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1918,c_1902]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_33,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.49/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1266,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_33]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1915,plain,
% 7.49/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1266]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_22,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1275,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.49/1.49      | ~ v1_funct_1(X0_57)
% 7.49/1.49      | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1907,plain,
% 7.49/1.49      ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
% 7.49/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.49/1.49      | v1_funct_1(X2_57) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1275]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3612,plain,
% 7.49/1.49      ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57)
% 7.49/1.49      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1915,c_1907]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_35,negated_conjecture,
% 7.49/1.49      ( v1_funct_1(sK6) ),
% 7.49/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2354,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.49/1.49      | ~ v1_funct_1(sK6)
% 7.49/1.49      | k2_partfun1(X0_57,X1_57,sK6,X2_57) = k7_relat_1(sK6,X2_57) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1275]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2529,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.49/1.49      | ~ v1_funct_1(sK6)
% 7.49/1.49      | k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2354]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3887,plain,
% 7.49/1.49      ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3612,c_35,c_33,c_2529]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3611,plain,
% 7.49/1.49      ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57)
% 7.49/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1912,c_1907]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2349,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.49/1.49      | ~ v1_funct_1(sK7)
% 7.49/1.49      | k2_partfun1(X0_57,X1_57,sK7,X2_57) = k7_relat_1(sK7,X2_57) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1275]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2524,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.49/1.49      | ~ v1_funct_1(sK7)
% 7.49/1.49      | k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2349]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3806,plain,
% 7.49/1.49      ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3611,c_32,c_30,c_2524]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_25,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.49/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_28,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_27,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_26,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_220,plain,
% 7.49/1.49      ( ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_25,c_28,c_27,c_26]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_221,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_220]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1257,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.49/1.49      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.49/1.49      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.49/1.49      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.49/1.49      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.49/1.49      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.49/1.49      | ~ v1_funct_1(X0_57)
% 7.49/1.49      | ~ v1_funct_1(X3_57)
% 7.49/1.49      | v1_xboole_0(X2_57)
% 7.49/1.49      | v1_xboole_0(X1_57)
% 7.49/1.49      | v1_xboole_0(X4_57)
% 7.49/1.49      | v1_xboole_0(X5_57)
% 7.49/1.49      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_221]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1924,plain,
% 7.49/1.49      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
% 7.49/1.49      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.49/1.49      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.49/1.49      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.49/1.49      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.49/1.49      | v1_funct_1(X2_57) != iProver_top
% 7.49/1.49      | v1_funct_1(X5_57) != iProver_top
% 7.49/1.49      | v1_xboole_0(X3_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X1_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X4_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7327,plain,
% 7.49/1.49      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.49/1.49      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.49/1.49      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | v1_funct_1(X1_57) != iProver_top
% 7.49/1.49      | v1_funct_1(sK7) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X2_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.49/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3806,c_1924]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_44,plain,
% 7.49/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_47,plain,
% 7.49/1.49      ( v1_xboole_0(sK5) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_53,plain,
% 7.49/1.49      ( v1_funct_1(sK7) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_54,plain,
% 7.49/1.49      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8090,plain,
% 7.49/1.49      ( v1_funct_1(X1_57) != iProver_top
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.49/1.49      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.49/1.49      | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X2_57) = iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_7327,c_44,c_47,c_53,c_54,c_55]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8091,plain,
% 7.49/1.49      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),X0_57) = X1_57
% 7.49/1.49      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | v1_funct_1(X1_57) != iProver_top
% 7.49/1.49      | v1_xboole_0(X2_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_8090]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8106,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.49/1.49      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.49/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.49/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | v1_funct_1(sK6) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3887,c_8091]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_45,plain,
% 7.49/1.49      ( v1_xboole_0(sK4) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_50,plain,
% 7.49/1.49      ( v1_funct_1(sK6) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_34,negated_conjecture,
% 7.49/1.49      ( v1_funct_2(sK6,sK4,sK3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_51,plain,
% 7.49/1.49      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_52,plain,
% 7.49/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8237,plain,
% 7.49/1.49      ( v1_xboole_0(X0_57) = iProver_top
% 7.49/1.49      | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.49/1.49      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_8106,c_45,c_50,c_51,c_52]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8238,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.49/1.49      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_8237]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8248,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.49/1.49      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2586,c_8238]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8249,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.49/1.49      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_8248,c_2586]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_42,negated_conjecture,
% 7.49/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.49/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_39,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8250,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 7.49/1.49      | v1_xboole_0(sK2)
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.49/1.49      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 7.49/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_8249]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8436,plain,
% 7.49/1.49      ( k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_8249,c_42,c_39,c_37,c_8250]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8437,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.49/1.49      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_8436]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13156,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.49/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_12770,c_8437]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_29,negated_conjecture,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.49/1.49      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1270,negated_conjecture,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.49/1.49      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_29]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2755,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.49/1.49      | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_2586,c_1270]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3810,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.49/1.49      | k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_3806,c_2755]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3891,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.49/1.49      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5)) ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_3810,c_3887]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13157,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.49/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_12770,c_3891]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13167,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.49/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.49/1.49      inference(backward_subsumption_resolution,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_13156,c_13157]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_24,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.49/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_227,plain,
% 7.49/1.49      ( ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_24,c_28,c_27,c_26]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_228,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X4)
% 7.49/1.49      | v1_xboole_0(X5)
% 7.49/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_227]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1256,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.49/1.49      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.49/1.49      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.49/1.49      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.49/1.49      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.49/1.49      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.49/1.49      | ~ v1_funct_1(X0_57)
% 7.49/1.49      | ~ v1_funct_1(X3_57)
% 7.49/1.49      | v1_xboole_0(X2_57)
% 7.49/1.49      | v1_xboole_0(X1_57)
% 7.49/1.49      | v1_xboole_0(X4_57)
% 7.49/1.49      | v1_xboole_0(X5_57)
% 7.49/1.49      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_228]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1925,plain,
% 7.49/1.49      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
% 7.49/1.49      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.49/1.49      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.49/1.49      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.49/1.49      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.49/1.49      | v1_funct_1(X2_57) != iProver_top
% 7.49/1.49      | v1_funct_1(X5_57) != iProver_top
% 7.49/1.49      | v1_xboole_0(X3_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X1_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X4_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8874,plain,
% 7.49/1.49      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.49/1.49      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.49/1.49      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | v1_funct_1(X1_57) != iProver_top
% 7.49/1.49      | v1_funct_1(sK7) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X2_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.49/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3806,c_1925]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13981,plain,
% 7.49/1.49      ( v1_funct_1(X1_57) != iProver_top
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.49/1.49      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.49/1.49      | k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X2_57) = iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_8874,c_44,c_47,c_53,c_54,c_55]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13982,plain,
% 7.49/1.49      ( k2_partfun1(X0_57,sK3,X1_57,k9_subset_1(X2_57,X0_57,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_57,X0_57,sK5))
% 7.49/1.49      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK5),sK3,k1_tmap_1(X2_57,sK3,X0_57,sK5,X1_57,sK7),sK5) = sK7
% 7.49/1.49      | v1_funct_2(X1_57,X0_57,sK3) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X2_57)) != iProver_top
% 7.49/1.49      | v1_funct_1(X1_57) != iProver_top
% 7.49/1.49      | v1_xboole_0(X2_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_13981]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13997,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.49/1.49      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.49/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.49/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | v1_funct_1(sK6) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.49/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3887,c_13982]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14091,plain,
% 7.49/1.49      ( v1_xboole_0(X0_57) = iProver_top
% 7.49/1.49      | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.49/1.49      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_13997,c_45,c_50,c_51,c_52]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14092,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.49/1.49      | k7_relat_1(sK7,k9_subset_1(X0_57,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_57,sK4,sK5))
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0_57)) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_14091]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14102,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.49/1.49      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2586,c_14092]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14103,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.49/1.49      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.49/1.49      inference(light_normalisation,[status(thm)],[c_14102,c_12770]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14104,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.49/1.49      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_14103,c_2586]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14105,plain,
% 7.49/1.49      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.49/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 7.49/1.49      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.49/1.49      inference(light_normalisation,[status(thm)],[c_14104,c_12770]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14106,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 7.49/1.49      | v1_xboole_0(sK2)
% 7.49/1.49      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.49/1.49      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.49/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_14105]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_20590,plain,
% 7.49/1.49      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_13156,c_42,c_39,c_37,c_13167,c_14106]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3,plain,
% 7.49/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1287,plain,
% 7.49/1.49      ( r2_hidden(sK0(X0_57,X1_57),X0_57) | r1_xboole_0(X0_57,X1_57) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1898,plain,
% 7.49/1.49      ( r2_hidden(sK0(X0_57,X1_57),X0_57) = iProver_top
% 7.49/1.49      | r1_xboole_0(X0_57,X1_57) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6,plain,
% 7.49/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.49/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1284,plain,
% 7.49/1.49      ( k3_xboole_0(X0_57,k1_xboole_0) = k1_xboole_0 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.49/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1286,plain,
% 7.49/1.49      ( ~ r2_hidden(X0_59,k3_xboole_0(X0_57,X1_57))
% 7.49/1.49      | ~ r1_xboole_0(X0_57,X1_57) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1899,plain,
% 7.49/1.49      ( r2_hidden(X0_59,k3_xboole_0(X0_57,X1_57)) != iProver_top
% 7.49/1.49      | r1_xboole_0(X0_57,X1_57) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1286]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3483,plain,
% 7.49/1.49      ( r2_hidden(X0_59,k1_xboole_0) != iProver_top
% 7.49/1.49      | r1_xboole_0(X0_57,k1_xboole_0) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1284,c_1899]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7,plain,
% 7.49/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1283,plain,
% 7.49/1.49      ( r1_xboole_0(X0_57,k1_xboole_0) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1343,plain,
% 7.49/1.49      ( r1_xboole_0(X0_57,k1_xboole_0) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1283]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3536,plain,
% 7.49/1.49      ( r2_hidden(X0_59,k1_xboole_0) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3483,c_1343]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3543,plain,
% 7.49/1.49      ( r1_xboole_0(k1_xboole_0,X0_57) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1898,c_3536]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12295,plain,
% 7.49/1.49      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3543,c_12287]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_10522,plain,
% 7.49/1.49      ( k1_relat_1(sK6) = sK4
% 7.49/1.49      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.49/1.49      | v1_funct_1(sK6) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1915,c_1927]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2344,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK6,X0_57,X1_57)
% 7.49/1.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.49/1.49      | ~ v1_funct_1(sK6)
% 7.49/1.49      | v1_xboole_0(X1_57)
% 7.49/1.49      | k1_relat_1(sK6) = X0_57 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1254]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2521,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK6,sK4,sK3)
% 7.49/1.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.49/1.49      | ~ v1_funct_1(sK6)
% 7.49/1.49      | v1_xboole_0(sK3)
% 7.49/1.49      | k1_relat_1(sK6) = sK4 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2344]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12040,plain,
% 7.49/1.49      ( k1_relat_1(sK6) = sK4 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_10522,c_41,c_35,c_34,c_33,c_2521]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12066,plain,
% 7.49/1.49      ( k7_relat_1(sK6,X0_57) = k1_xboole_0
% 7.49/1.49      | r1_xboole_0(X0_57,sK4) != iProver_top
% 7.49/1.49      | v1_relat_1(sK6) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_12040,c_1903]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2280,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.49/1.49      | v1_relat_1(sK6) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1276]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2281,plain,
% 7.49/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.49/1.49      | v1_relat_1(sK6) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_2280]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12776,plain,
% 7.49/1.49      ( r1_xboole_0(X0_57,sK4) != iProver_top
% 7.49/1.49      | k7_relat_1(sK6,X0_57) = k1_xboole_0 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_12066,c_52,c_2281]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12777,plain,
% 7.49/1.49      ( k7_relat_1(sK6,X0_57) = k1_xboole_0
% 7.49/1.49      | r1_xboole_0(X0_57,sK4) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_12776]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12784,plain,
% 7.49/1.49      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3543,c_12777]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_20592,plain,
% 7.49/1.49      ( k1_xboole_0 != k1_xboole_0 ),
% 7.49/1.49      inference(light_normalisation,[status(thm)],[c_20590,c_12295,c_12784]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_20593,plain,
% 7.49/1.49      ( $false ),
% 7.49/1.49      inference(equality_resolution_simp,[status(thm)],[c_20592]) ).
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  ------                               Statistics
% 7.49/1.49  
% 7.49/1.49  ------ General
% 7.49/1.49  
% 7.49/1.49  abstr_ref_over_cycles:                  0
% 7.49/1.49  abstr_ref_under_cycles:                 0
% 7.49/1.49  gc_basic_clause_elim:                   0
% 7.49/1.49  forced_gc_time:                         0
% 7.49/1.49  parsing_time:                           0.012
% 7.49/1.49  unif_index_cands_time:                  0.
% 7.49/1.49  unif_index_add_time:                    0.
% 7.49/1.49  orderings_time:                         0.
% 7.49/1.49  out_proof_time:                         0.017
% 7.49/1.49  total_time:                             1.004
% 7.49/1.49  num_of_symbols:                         63
% 7.49/1.49  num_of_terms:                           38161
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing
% 7.49/1.49  
% 7.49/1.49  num_of_splits:                          0
% 7.49/1.49  num_of_split_atoms:                     0
% 7.49/1.49  num_of_reused_defs:                     0
% 7.49/1.49  num_eq_ax_congr_red:                    21
% 7.49/1.49  num_of_sem_filtered_clauses:            1
% 7.49/1.49  num_of_subtypes:                        3
% 7.49/1.49  monotx_restored_types:                  0
% 7.49/1.49  sat_num_of_epr_types:                   0
% 7.49/1.49  sat_num_of_non_cyclic_types:            0
% 7.49/1.49  sat_guarded_non_collapsed_types:        1
% 7.49/1.49  num_pure_diseq_elim:                    0
% 7.49/1.49  simp_replaced_by:                       0
% 7.49/1.49  res_preprocessed:                       194
% 7.49/1.49  prep_upred:                             0
% 7.49/1.49  prep_unflattend:                        64
% 7.49/1.49  smt_new_axioms:                         0
% 7.49/1.49  pred_elim_cands:                        7
% 7.49/1.49  pred_elim:                              3
% 7.49/1.49  pred_elim_cl:                           5
% 7.49/1.49  pred_elim_cycles:                       7
% 7.49/1.49  merged_defs:                            0
% 7.49/1.49  merged_defs_ncl:                        0
% 7.49/1.49  bin_hyper_res:                          0
% 7.49/1.49  prep_cycles:                            4
% 7.49/1.49  pred_elim_time:                         0.01
% 7.49/1.49  splitting_time:                         0.
% 7.49/1.49  sem_filter_time:                        0.
% 7.49/1.49  monotx_time:                            0.
% 7.49/1.49  subtype_inf_time:                       0.002
% 7.49/1.49  
% 7.49/1.49  ------ Problem properties
% 7.49/1.49  
% 7.49/1.49  clauses:                                37
% 7.49/1.49  conjectures:                            13
% 7.49/1.49  epr:                                    11
% 7.49/1.49  horn:                                   27
% 7.49/1.49  ground:                                 16
% 7.49/1.49  unary:                                  18
% 7.49/1.49  binary:                                 8
% 7.49/1.49  lits:                                   135
% 7.49/1.49  lits_eq:                                19
% 7.49/1.49  fd_pure:                                0
% 7.49/1.49  fd_pseudo:                              0
% 7.49/1.49  fd_cond:                                0
% 7.49/1.49  fd_pseudo_cond:                         1
% 7.49/1.49  ac_symbols:                             0
% 7.49/1.49  
% 7.49/1.49  ------ Propositional Solver
% 7.49/1.49  
% 7.49/1.49  prop_solver_calls:                      28
% 7.49/1.49  prop_fast_solver_calls:                 3238
% 7.49/1.49  smt_solver_calls:                       0
% 7.49/1.49  smt_fast_solver_calls:                  0
% 7.49/1.49  prop_num_of_clauses:                    7713
% 7.49/1.49  prop_preprocess_simplified:             13156
% 7.49/1.49  prop_fo_subsumed:                       178
% 7.49/1.49  prop_solver_time:                       0.
% 7.49/1.49  smt_solver_time:                        0.
% 7.49/1.49  smt_fast_solver_time:                   0.
% 7.49/1.49  prop_fast_solver_time:                  0.
% 7.49/1.49  prop_unsat_core_time:                   0.
% 7.49/1.49  
% 7.49/1.49  ------ QBF
% 7.49/1.49  
% 7.49/1.49  qbf_q_res:                              0
% 7.49/1.49  qbf_num_tautologies:                    0
% 7.49/1.49  qbf_prep_cycles:                        0
% 7.49/1.49  
% 7.49/1.49  ------ BMC1
% 7.49/1.49  
% 7.49/1.49  bmc1_current_bound:                     -1
% 7.49/1.49  bmc1_last_solved_bound:                 -1
% 7.49/1.49  bmc1_unsat_core_size:                   -1
% 7.49/1.49  bmc1_unsat_core_parents_size:           -1
% 7.49/1.49  bmc1_merge_next_fun:                    0
% 7.49/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.49/1.49  
% 7.49/1.49  ------ Instantiation
% 7.49/1.49  
% 7.49/1.49  inst_num_of_clauses:                    1682
% 7.49/1.49  inst_num_in_passive:                    203
% 7.49/1.49  inst_num_in_active:                     824
% 7.49/1.49  inst_num_in_unprocessed:                655
% 7.49/1.49  inst_num_of_loops:                      940
% 7.49/1.49  inst_num_of_learning_restarts:          0
% 7.49/1.49  inst_num_moves_active_passive:          112
% 7.49/1.49  inst_lit_activity:                      0
% 7.49/1.49  inst_lit_activity_moves:                1
% 7.49/1.49  inst_num_tautologies:                   0
% 7.49/1.49  inst_num_prop_implied:                  0
% 7.49/1.49  inst_num_existing_simplified:           0
% 7.49/1.49  inst_num_eq_res_simplified:             0
% 7.49/1.49  inst_num_child_elim:                    0
% 7.49/1.49  inst_num_of_dismatching_blockings:      236
% 7.49/1.49  inst_num_of_non_proper_insts:           1177
% 7.49/1.49  inst_num_of_duplicates:                 0
% 7.49/1.49  inst_inst_num_from_inst_to_res:         0
% 7.49/1.49  inst_dismatching_checking_time:         0.
% 7.49/1.49  
% 7.49/1.49  ------ Resolution
% 7.49/1.49  
% 7.49/1.49  res_num_of_clauses:                     0
% 7.49/1.49  res_num_in_passive:                     0
% 7.49/1.49  res_num_in_active:                      0
% 7.49/1.49  res_num_of_loops:                       198
% 7.49/1.49  res_forward_subset_subsumed:            36
% 7.49/1.49  res_backward_subset_subsumed:           0
% 7.49/1.49  res_forward_subsumed:                   0
% 7.49/1.49  res_backward_subsumed:                  0
% 7.49/1.49  res_forward_subsumption_resolution:     1
% 7.49/1.49  res_backward_subsumption_resolution:    0
% 7.49/1.49  res_clause_to_clause_subsumption:       2013
% 7.49/1.49  res_orphan_elimination:                 0
% 7.49/1.49  res_tautology_del:                      30
% 7.49/1.49  res_num_eq_res_simplified:              0
% 7.49/1.49  res_num_sel_changes:                    0
% 7.49/1.49  res_moves_from_active_to_pass:          0
% 7.49/1.49  
% 7.49/1.49  ------ Superposition
% 7.49/1.49  
% 7.49/1.49  sup_time_total:                         0.
% 7.49/1.49  sup_time_generating:                    0.
% 7.49/1.49  sup_time_sim_full:                      0.
% 7.49/1.49  sup_time_sim_immed:                     0.
% 7.49/1.49  
% 7.49/1.49  sup_num_of_clauses:                     336
% 7.49/1.49  sup_num_in_active:                      133
% 7.49/1.49  sup_num_in_passive:                     203
% 7.49/1.49  sup_num_of_loops:                       187
% 7.49/1.49  sup_fw_superposition:                   638
% 7.49/1.49  sup_bw_superposition:                   207
% 7.49/1.49  sup_immediate_simplified:               293
% 7.49/1.49  sup_given_eliminated:                   0
% 7.49/1.49  comparisons_done:                       0
% 7.49/1.49  comparisons_avoided:                    0
% 7.49/1.49  
% 7.49/1.49  ------ Simplifications
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  sim_fw_subset_subsumed:                 21
% 7.49/1.49  sim_bw_subset_subsumed:                 1
% 7.49/1.49  sim_fw_subsumed:                        60
% 7.49/1.49  sim_bw_subsumed:                        0
% 7.49/1.49  sim_fw_subsumption_res:                 1
% 7.49/1.49  sim_bw_subsumption_res:                 1
% 7.49/1.49  sim_tautology_del:                      6
% 7.49/1.49  sim_eq_tautology_del:                   8
% 7.49/1.49  sim_eq_res_simp:                        1
% 7.49/1.49  sim_fw_demodulated:                     90
% 7.49/1.49  sim_bw_demodulated:                     55
% 7.49/1.49  sim_light_normalised:                   141
% 7.49/1.49  sim_joinable_taut:                      0
% 7.49/1.49  sim_joinable_simp:                      0
% 7.49/1.49  sim_ac_normalised:                      0
% 7.49/1.49  sim_smt_subsumption:                    0
% 7.49/1.49  
%------------------------------------------------------------------------------
