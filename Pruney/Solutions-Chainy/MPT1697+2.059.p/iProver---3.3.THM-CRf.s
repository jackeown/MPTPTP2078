%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:35 EST 2020

% Result     : Theorem 7.33s
% Output     : CNFRefutation 7.33s
% Verified   : 
% Statistics : Number of formulae       :  255 (3665 expanded)
%              Number of clauses        :  155 (1028 expanded)
%              Number of leaves         :   26 (1239 expanded)
%              Depth                    :   26
%              Number of atoms          : 1189 (36586 expanded)
%              Number of equality atoms :  483 (9042 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

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
    inference(ennf_transformation,[],[f22])).

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

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4
          | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK5,X3,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4
              | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK4,X2,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4
                  | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
                & v1_funct_2(X5,sK3,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
                    ( ( k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4
                      | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
                & v1_funct_2(X4,sK2,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                        & v1_funct_2(X5,X3,sK1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                    & v1_funct_2(X4,X2,sK1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
                          ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK5,sK3,sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & r1_subset_1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f61,f60,f59,f58,f57,f56])).

fof(f100,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f104,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f102,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f107,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f105,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f115,plain,(
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
    inference(equality_resolution,[],[f90])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

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

fof(f92,plain,(
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

fof(f93,plain,(
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

fof(f94,plain,(
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

fof(f96,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f106,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f103,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f116,plain,(
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
    inference(equality_resolution,[],[f89])).

fof(f108,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f95,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2127,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3732,plain,
    ( r1_tarski(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_2146])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_330,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_421,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_330])).

cnf(c_2118,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_17336,plain,
    ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_3732,c_2118])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2130,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2138,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6428,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2130,c_2138])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2623,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2835,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2623])).

cnf(c_7139,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6428,c_38,c_36,c_2835])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2133,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6427,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2133,c_2138])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2618,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2829,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_6824,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6427,c_35,c_33,c_2829])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f115])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f92])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f93])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f94])).

cnf(c_246,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_31,c_30,c_29])).

cnf(c_247,plain,
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
    inference(renaming,[status(thm)],[c_246])).

cnf(c_2120,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_6830,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6824,c_2120])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_47,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_50,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_56,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_57,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7850,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6830,c_47,c_50,c_56,c_57,c_58])).

cnf(c_7851,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7850])).

cnf(c_7866,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7139,c_7851])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_48,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_53,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_54,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_55,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7889,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7866,c_48,c_53,c_54,c_55])).

cnf(c_7890,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7889])).

cnf(c_17927,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17336,c_7890])).

cnf(c_22,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_588,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_39])).

cnf(c_589,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_591,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_43,c_41])).

cnf(c_2116,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2151,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3388,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2116,c_2151])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3918,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2133,c_2139])).

cnf(c_3919,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2130,c_2139])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2143,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5655,plain,
    ( k7_relat_1(k7_relat_1(X0,sK2),sK3) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2116,c_2143])).

cnf(c_5736,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3919,c_5655])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_24,c_17])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_24,c_23,c_17])).

cnf(c_2117,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_3312,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_2130,c_2117])).

cnf(c_5738,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5736,c_3312])).

cnf(c_20,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2140,plain,
    ( k7_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5748,plain,
    ( r1_xboole_0(k1_relat_1(sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5738,c_2140])).

cnf(c_2545,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2546,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2545])).

cnf(c_5904,plain,
    ( r1_xboole_0(k1_relat_1(sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5748,c_55,c_2546])).

cnf(c_5909,plain,
    ( k3_xboole_0(k1_relat_1(sK4),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5904,c_2151])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2142,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4537,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = k3_xboole_0(k1_relat_1(sK4),X0) ),
    inference(superposition,[status(thm)],[c_3919,c_2142])).

cnf(c_7702,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5909,c_4537])).

cnf(c_7704,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7702,c_5738])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2148,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3313,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2117])).

cnf(c_3862,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2147,c_3313])).

cnf(c_4370,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2148,c_3862])).

cnf(c_4648,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4370,c_2140])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_108,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_110,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_123,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_124,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1224,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2641,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_2642,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2641])).

cnf(c_2644,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2642])).

cnf(c_1217,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2986,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_2987,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2986])).

cnf(c_9563,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4648,c_110,c_123,c_124,c_2644,c_2987])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2150,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9571,plain,
    ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9563,c_2150])).

cnf(c_10865,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7704,c_9571])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2141,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12070,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10865,c_2141])).

cnf(c_13210,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3918,c_12070])).

cnf(c_18067,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17927,c_3388,c_13210])).

cnf(c_18068,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18067,c_17336])).

cnf(c_13211,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3919,c_12070])).

cnf(c_18069,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18068,c_3388,c_13211])).

cnf(c_18070,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18069])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f116])).

cnf(c_239,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_31,c_30,c_29])).

cnf(c_240,plain,
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
    inference(renaming,[status(thm)],[c_239])).

cnf(c_2121,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_6829,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6824,c_2121])).

cnf(c_7363,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6829,c_47,c_50,c_56,c_57,c_58])).

cnf(c_7364,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7363])).

cnf(c_7379,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7139,c_7364])).

cnf(c_7481,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7379,c_48,c_53,c_54,c_55])).

cnf(c_7482,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7481])).

cnf(c_17928,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17336,c_7482])).

cnf(c_18054,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17928,c_3388,c_13210])).

cnf(c_18055,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18054,c_17336])).

cnf(c_18056,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18055,c_3388,c_13211])).

cnf(c_18057,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18056])).

cnf(c_32,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_6828,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_6824,c_32])).

cnf(c_7143,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_7139,c_6828])).

cnf(c_17918,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_17336,c_7143])).

cnf(c_17919,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17918,c_3388,c_13210,c_13211])).

cnf(c_17920,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_17919])).

cnf(c_51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_46,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18070,c_18057,c_17920,c_51,c_49,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.33/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.33/1.50  
% 7.33/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.33/1.50  
% 7.33/1.50  ------  iProver source info
% 7.33/1.50  
% 7.33/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.33/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.33/1.50  git: non_committed_changes: false
% 7.33/1.50  git: last_make_outside_of_git: false
% 7.33/1.50  
% 7.33/1.50  ------ 
% 7.33/1.50  
% 7.33/1.50  ------ Input Options
% 7.33/1.50  
% 7.33/1.50  --out_options                           all
% 7.33/1.50  --tptp_safe_out                         true
% 7.33/1.50  --problem_path                          ""
% 7.33/1.50  --include_path                          ""
% 7.33/1.50  --clausifier                            res/vclausify_rel
% 7.33/1.50  --clausifier_options                    --mode clausify
% 7.33/1.50  --stdin                                 false
% 7.33/1.50  --stats_out                             all
% 7.33/1.50  
% 7.33/1.50  ------ General Options
% 7.33/1.50  
% 7.33/1.50  --fof                                   false
% 7.33/1.50  --time_out_real                         305.
% 7.33/1.50  --time_out_virtual                      -1.
% 7.33/1.50  --symbol_type_check                     false
% 7.33/1.50  --clausify_out                          false
% 7.33/1.50  --sig_cnt_out                           false
% 7.33/1.50  --trig_cnt_out                          false
% 7.33/1.50  --trig_cnt_out_tolerance                1.
% 7.33/1.50  --trig_cnt_out_sk_spl                   false
% 7.33/1.50  --abstr_cl_out                          false
% 7.33/1.50  
% 7.33/1.50  ------ Global Options
% 7.33/1.50  
% 7.33/1.50  --schedule                              default
% 7.33/1.50  --add_important_lit                     false
% 7.33/1.50  --prop_solver_per_cl                    1000
% 7.33/1.50  --min_unsat_core                        false
% 7.33/1.50  --soft_assumptions                      false
% 7.33/1.50  --soft_lemma_size                       3
% 7.33/1.50  --prop_impl_unit_size                   0
% 7.33/1.50  --prop_impl_unit                        []
% 7.33/1.50  --share_sel_clauses                     true
% 7.33/1.50  --reset_solvers                         false
% 7.33/1.50  --bc_imp_inh                            [conj_cone]
% 7.33/1.50  --conj_cone_tolerance                   3.
% 7.33/1.50  --extra_neg_conj                        none
% 7.33/1.50  --large_theory_mode                     true
% 7.33/1.50  --prolific_symb_bound                   200
% 7.33/1.50  --lt_threshold                          2000
% 7.33/1.50  --clause_weak_htbl                      true
% 7.33/1.50  --gc_record_bc_elim                     false
% 7.33/1.50  
% 7.33/1.50  ------ Preprocessing Options
% 7.33/1.50  
% 7.33/1.50  --preprocessing_flag                    true
% 7.33/1.50  --time_out_prep_mult                    0.1
% 7.33/1.50  --splitting_mode                        input
% 7.33/1.50  --splitting_grd                         true
% 7.33/1.50  --splitting_cvd                         false
% 7.33/1.50  --splitting_cvd_svl                     false
% 7.33/1.50  --splitting_nvd                         32
% 7.33/1.50  --sub_typing                            true
% 7.33/1.50  --prep_gs_sim                           true
% 7.33/1.50  --prep_unflatten                        true
% 7.33/1.50  --prep_res_sim                          true
% 7.33/1.50  --prep_upred                            true
% 7.33/1.50  --prep_sem_filter                       exhaustive
% 7.33/1.50  --prep_sem_filter_out                   false
% 7.33/1.50  --pred_elim                             true
% 7.33/1.50  --res_sim_input                         true
% 7.33/1.50  --eq_ax_congr_red                       true
% 7.33/1.50  --pure_diseq_elim                       true
% 7.33/1.50  --brand_transform                       false
% 7.33/1.50  --non_eq_to_eq                          false
% 7.33/1.50  --prep_def_merge                        true
% 7.33/1.50  --prep_def_merge_prop_impl              false
% 7.33/1.50  --prep_def_merge_mbd                    true
% 7.33/1.50  --prep_def_merge_tr_red                 false
% 7.33/1.50  --prep_def_merge_tr_cl                  false
% 7.33/1.50  --smt_preprocessing                     true
% 7.33/1.50  --smt_ac_axioms                         fast
% 7.33/1.50  --preprocessed_out                      false
% 7.33/1.50  --preprocessed_stats                    false
% 7.33/1.50  
% 7.33/1.50  ------ Abstraction refinement Options
% 7.33/1.50  
% 7.33/1.50  --abstr_ref                             []
% 7.33/1.50  --abstr_ref_prep                        false
% 7.33/1.50  --abstr_ref_until_sat                   false
% 7.33/1.50  --abstr_ref_sig_restrict                funpre
% 7.33/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.50  --abstr_ref_under                       []
% 7.33/1.50  
% 7.33/1.50  ------ SAT Options
% 7.33/1.50  
% 7.33/1.50  --sat_mode                              false
% 7.33/1.50  --sat_fm_restart_options                ""
% 7.33/1.50  --sat_gr_def                            false
% 7.33/1.50  --sat_epr_types                         true
% 7.33/1.50  --sat_non_cyclic_types                  false
% 7.33/1.50  --sat_finite_models                     false
% 7.33/1.50  --sat_fm_lemmas                         false
% 7.33/1.50  --sat_fm_prep                           false
% 7.33/1.50  --sat_fm_uc_incr                        true
% 7.33/1.50  --sat_out_model                         small
% 7.33/1.50  --sat_out_clauses                       false
% 7.33/1.50  
% 7.33/1.50  ------ QBF Options
% 7.33/1.50  
% 7.33/1.50  --qbf_mode                              false
% 7.33/1.50  --qbf_elim_univ                         false
% 7.33/1.50  --qbf_dom_inst                          none
% 7.33/1.50  --qbf_dom_pre_inst                      false
% 7.33/1.50  --qbf_sk_in                             false
% 7.33/1.50  --qbf_pred_elim                         true
% 7.33/1.50  --qbf_split                             512
% 7.33/1.50  
% 7.33/1.50  ------ BMC1 Options
% 7.33/1.50  
% 7.33/1.50  --bmc1_incremental                      false
% 7.33/1.50  --bmc1_axioms                           reachable_all
% 7.33/1.50  --bmc1_min_bound                        0
% 7.33/1.50  --bmc1_max_bound                        -1
% 7.33/1.50  --bmc1_max_bound_default                -1
% 7.33/1.50  --bmc1_symbol_reachability              true
% 7.33/1.50  --bmc1_property_lemmas                  false
% 7.33/1.50  --bmc1_k_induction                      false
% 7.33/1.50  --bmc1_non_equiv_states                 false
% 7.33/1.50  --bmc1_deadlock                         false
% 7.33/1.50  --bmc1_ucm                              false
% 7.33/1.50  --bmc1_add_unsat_core                   none
% 7.33/1.50  --bmc1_unsat_core_children              false
% 7.33/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.33/1.50  --bmc1_out_stat                         full
% 7.33/1.50  --bmc1_ground_init                      false
% 7.33/1.50  --bmc1_pre_inst_next_state              false
% 7.33/1.50  --bmc1_pre_inst_state                   false
% 7.33/1.50  --bmc1_pre_inst_reach_state             false
% 7.33/1.50  --bmc1_out_unsat_core                   false
% 7.33/1.50  --bmc1_aig_witness_out                  false
% 7.33/1.50  --bmc1_verbose                          false
% 7.33/1.50  --bmc1_dump_clauses_tptp                false
% 7.33/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.33/1.50  --bmc1_dump_file                        -
% 7.33/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.33/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.33/1.50  --bmc1_ucm_extend_mode                  1
% 7.33/1.50  --bmc1_ucm_init_mode                    2
% 7.33/1.50  --bmc1_ucm_cone_mode                    none
% 7.33/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.33/1.50  --bmc1_ucm_relax_model                  4
% 7.33/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.33/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.33/1.50  --bmc1_ucm_layered_model                none
% 7.33/1.50  --bmc1_ucm_max_lemma_size               10
% 7.33/1.50  
% 7.33/1.50  ------ AIG Options
% 7.33/1.50  
% 7.33/1.50  --aig_mode                              false
% 7.33/1.50  
% 7.33/1.50  ------ Instantiation Options
% 7.33/1.50  
% 7.33/1.50  --instantiation_flag                    true
% 7.33/1.50  --inst_sos_flag                         false
% 7.33/1.50  --inst_sos_phase                        true
% 7.33/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.33/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.33/1.50  --inst_lit_sel_side                     num_symb
% 7.33/1.50  --inst_solver_per_active                1400
% 7.33/1.50  --inst_solver_calls_frac                1.
% 7.33/1.50  --inst_passive_queue_type               priority_queues
% 7.33/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.33/1.50  --inst_passive_queues_freq              [25;2]
% 7.33/1.50  --inst_dismatching                      true
% 7.33/1.50  --inst_eager_unprocessed_to_passive     true
% 7.33/1.50  --inst_prop_sim_given                   true
% 7.33/1.50  --inst_prop_sim_new                     false
% 7.33/1.50  --inst_subs_new                         false
% 7.33/1.50  --inst_eq_res_simp                      false
% 7.33/1.50  --inst_subs_given                       false
% 7.33/1.50  --inst_orphan_elimination               true
% 7.33/1.50  --inst_learning_loop_flag               true
% 7.33/1.50  --inst_learning_start                   3000
% 7.33/1.50  --inst_learning_factor                  2
% 7.33/1.50  --inst_start_prop_sim_after_learn       3
% 7.33/1.50  --inst_sel_renew                        solver
% 7.33/1.50  --inst_lit_activity_flag                true
% 7.33/1.50  --inst_restr_to_given                   false
% 7.33/1.50  --inst_activity_threshold               500
% 7.33/1.50  --inst_out_proof                        true
% 7.33/1.50  
% 7.33/1.50  ------ Resolution Options
% 7.33/1.50  
% 7.33/1.50  --resolution_flag                       true
% 7.33/1.50  --res_lit_sel                           adaptive
% 7.33/1.50  --res_lit_sel_side                      none
% 7.33/1.50  --res_ordering                          kbo
% 7.33/1.50  --res_to_prop_solver                    active
% 7.33/1.50  --res_prop_simpl_new                    false
% 7.33/1.50  --res_prop_simpl_given                  true
% 7.33/1.50  --res_passive_queue_type                priority_queues
% 7.33/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.33/1.50  --res_passive_queues_freq               [15;5]
% 7.33/1.50  --res_forward_subs                      full
% 7.33/1.50  --res_backward_subs                     full
% 7.33/1.50  --res_forward_subs_resolution           true
% 7.33/1.50  --res_backward_subs_resolution          true
% 7.33/1.50  --res_orphan_elimination                true
% 7.33/1.50  --res_time_limit                        2.
% 7.33/1.50  --res_out_proof                         true
% 7.33/1.50  
% 7.33/1.50  ------ Superposition Options
% 7.33/1.50  
% 7.33/1.50  --superposition_flag                    true
% 7.33/1.50  --sup_passive_queue_type                priority_queues
% 7.33/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.33/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.33/1.50  --demod_completeness_check              fast
% 7.33/1.50  --demod_use_ground                      true
% 7.33/1.50  --sup_to_prop_solver                    passive
% 7.33/1.50  --sup_prop_simpl_new                    true
% 7.33/1.50  --sup_prop_simpl_given                  true
% 7.33/1.50  --sup_fun_splitting                     false
% 7.33/1.50  --sup_smt_interval                      50000
% 7.33/1.50  
% 7.33/1.50  ------ Superposition Simplification Setup
% 7.33/1.50  
% 7.33/1.50  --sup_indices_passive                   []
% 7.33/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.33/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.50  --sup_full_bw                           [BwDemod]
% 7.33/1.50  --sup_immed_triv                        [TrivRules]
% 7.33/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.50  --sup_immed_bw_main                     []
% 7.33/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.33/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.33/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.33/1.50  
% 7.33/1.50  ------ Combination Options
% 7.33/1.50  
% 7.33/1.50  --comb_res_mult                         3
% 7.33/1.50  --comb_sup_mult                         2
% 7.33/1.50  --comb_inst_mult                        10
% 7.33/1.50  
% 7.33/1.50  ------ Debug Options
% 7.33/1.50  
% 7.33/1.50  --dbg_backtrace                         false
% 7.33/1.50  --dbg_dump_prop_clauses                 false
% 7.33/1.50  --dbg_dump_prop_clauses_file            -
% 7.33/1.50  --dbg_out_stat                          false
% 7.33/1.50  ------ Parsing...
% 7.33/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.33/1.50  
% 7.33/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.33/1.50  
% 7.33/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.33/1.50  
% 7.33/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.33/1.50  ------ Proving...
% 7.33/1.50  ------ Problem Properties 
% 7.33/1.50  
% 7.33/1.50  
% 7.33/1.50  clauses                                 42
% 7.33/1.50  conjectures                             13
% 7.33/1.50  EPR                                     12
% 7.33/1.50  Horn                                    35
% 7.33/1.50  unary                                   18
% 7.33/1.50  binary                                  10
% 7.33/1.50  lits                                    146
% 7.33/1.50  lits eq                                 27
% 7.33/1.50  fd_pure                                 0
% 7.33/1.50  fd_pseudo                               0
% 7.33/1.50  fd_cond                                 1
% 7.33/1.50  fd_pseudo_cond                          1
% 7.33/1.50  AC symbols                              0
% 7.33/1.50  
% 7.33/1.50  ------ Schedule dynamic 5 is on 
% 7.33/1.50  
% 7.33/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.33/1.50  
% 7.33/1.50  
% 7.33/1.50  ------ 
% 7.33/1.50  Current options:
% 7.33/1.50  ------ 
% 7.33/1.50  
% 7.33/1.50  ------ Input Options
% 7.33/1.50  
% 7.33/1.50  --out_options                           all
% 7.33/1.50  --tptp_safe_out                         true
% 7.33/1.50  --problem_path                          ""
% 7.33/1.50  --include_path                          ""
% 7.33/1.50  --clausifier                            res/vclausify_rel
% 7.33/1.50  --clausifier_options                    --mode clausify
% 7.33/1.50  --stdin                                 false
% 7.33/1.50  --stats_out                             all
% 7.33/1.50  
% 7.33/1.50  ------ General Options
% 7.33/1.50  
% 7.33/1.50  --fof                                   false
% 7.33/1.50  --time_out_real                         305.
% 7.33/1.50  --time_out_virtual                      -1.
% 7.33/1.50  --symbol_type_check                     false
% 7.33/1.50  --clausify_out                          false
% 7.33/1.50  --sig_cnt_out                           false
% 7.33/1.50  --trig_cnt_out                          false
% 7.33/1.50  --trig_cnt_out_tolerance                1.
% 7.33/1.50  --trig_cnt_out_sk_spl                   false
% 7.33/1.50  --abstr_cl_out                          false
% 7.33/1.50  
% 7.33/1.50  ------ Global Options
% 7.33/1.50  
% 7.33/1.50  --schedule                              default
% 7.33/1.50  --add_important_lit                     false
% 7.33/1.50  --prop_solver_per_cl                    1000
% 7.33/1.50  --min_unsat_core                        false
% 7.33/1.50  --soft_assumptions                      false
% 7.33/1.50  --soft_lemma_size                       3
% 7.33/1.50  --prop_impl_unit_size                   0
% 7.33/1.50  --prop_impl_unit                        []
% 7.33/1.50  --share_sel_clauses                     true
% 7.33/1.50  --reset_solvers                         false
% 7.33/1.50  --bc_imp_inh                            [conj_cone]
% 7.33/1.50  --conj_cone_tolerance                   3.
% 7.33/1.50  --extra_neg_conj                        none
% 7.33/1.50  --large_theory_mode                     true
% 7.33/1.50  --prolific_symb_bound                   200
% 7.33/1.50  --lt_threshold                          2000
% 7.33/1.50  --clause_weak_htbl                      true
% 7.33/1.50  --gc_record_bc_elim                     false
% 7.33/1.50  
% 7.33/1.50  ------ Preprocessing Options
% 7.33/1.50  
% 7.33/1.50  --preprocessing_flag                    true
% 7.33/1.50  --time_out_prep_mult                    0.1
% 7.33/1.50  --splitting_mode                        input
% 7.33/1.50  --splitting_grd                         true
% 7.33/1.50  --splitting_cvd                         false
% 7.33/1.50  --splitting_cvd_svl                     false
% 7.33/1.50  --splitting_nvd                         32
% 7.33/1.50  --sub_typing                            true
% 7.33/1.50  --prep_gs_sim                           true
% 7.33/1.50  --prep_unflatten                        true
% 7.33/1.50  --prep_res_sim                          true
% 7.33/1.50  --prep_upred                            true
% 7.33/1.50  --prep_sem_filter                       exhaustive
% 7.33/1.50  --prep_sem_filter_out                   false
% 7.33/1.50  --pred_elim                             true
% 7.33/1.50  --res_sim_input                         true
% 7.33/1.50  --eq_ax_congr_red                       true
% 7.33/1.50  --pure_diseq_elim                       true
% 7.33/1.50  --brand_transform                       false
% 7.33/1.50  --non_eq_to_eq                          false
% 7.33/1.50  --prep_def_merge                        true
% 7.33/1.50  --prep_def_merge_prop_impl              false
% 7.33/1.50  --prep_def_merge_mbd                    true
% 7.33/1.50  --prep_def_merge_tr_red                 false
% 7.33/1.50  --prep_def_merge_tr_cl                  false
% 7.33/1.50  --smt_preprocessing                     true
% 7.33/1.50  --smt_ac_axioms                         fast
% 7.33/1.50  --preprocessed_out                      false
% 7.33/1.50  --preprocessed_stats                    false
% 7.33/1.50  
% 7.33/1.50  ------ Abstraction refinement Options
% 7.33/1.50  
% 7.33/1.50  --abstr_ref                             []
% 7.33/1.50  --abstr_ref_prep                        false
% 7.33/1.50  --abstr_ref_until_sat                   false
% 7.33/1.50  --abstr_ref_sig_restrict                funpre
% 7.33/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.50  --abstr_ref_under                       []
% 7.33/1.50  
% 7.33/1.50  ------ SAT Options
% 7.33/1.50  
% 7.33/1.50  --sat_mode                              false
% 7.33/1.50  --sat_fm_restart_options                ""
% 7.33/1.50  --sat_gr_def                            false
% 7.33/1.50  --sat_epr_types                         true
% 7.33/1.50  --sat_non_cyclic_types                  false
% 7.33/1.50  --sat_finite_models                     false
% 7.33/1.50  --sat_fm_lemmas                         false
% 7.33/1.50  --sat_fm_prep                           false
% 7.33/1.50  --sat_fm_uc_incr                        true
% 7.33/1.50  --sat_out_model                         small
% 7.33/1.50  --sat_out_clauses                       false
% 7.33/1.50  
% 7.33/1.50  ------ QBF Options
% 7.33/1.50  
% 7.33/1.50  --qbf_mode                              false
% 7.33/1.50  --qbf_elim_univ                         false
% 7.33/1.50  --qbf_dom_inst                          none
% 7.33/1.50  --qbf_dom_pre_inst                      false
% 7.33/1.50  --qbf_sk_in                             false
% 7.33/1.50  --qbf_pred_elim                         true
% 7.33/1.50  --qbf_split                             512
% 7.33/1.50  
% 7.33/1.50  ------ BMC1 Options
% 7.33/1.50  
% 7.33/1.50  --bmc1_incremental                      false
% 7.33/1.50  --bmc1_axioms                           reachable_all
% 7.33/1.50  --bmc1_min_bound                        0
% 7.33/1.50  --bmc1_max_bound                        -1
% 7.33/1.50  --bmc1_max_bound_default                -1
% 7.33/1.50  --bmc1_symbol_reachability              true
% 7.33/1.50  --bmc1_property_lemmas                  false
% 7.33/1.50  --bmc1_k_induction                      false
% 7.33/1.50  --bmc1_non_equiv_states                 false
% 7.33/1.50  --bmc1_deadlock                         false
% 7.33/1.50  --bmc1_ucm                              false
% 7.33/1.50  --bmc1_add_unsat_core                   none
% 7.33/1.50  --bmc1_unsat_core_children              false
% 7.33/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.33/1.50  --bmc1_out_stat                         full
% 7.33/1.50  --bmc1_ground_init                      false
% 7.33/1.50  --bmc1_pre_inst_next_state              false
% 7.33/1.50  --bmc1_pre_inst_state                   false
% 7.33/1.50  --bmc1_pre_inst_reach_state             false
% 7.33/1.50  --bmc1_out_unsat_core                   false
% 7.33/1.50  --bmc1_aig_witness_out                  false
% 7.33/1.50  --bmc1_verbose                          false
% 7.33/1.50  --bmc1_dump_clauses_tptp                false
% 7.33/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.33/1.50  --bmc1_dump_file                        -
% 7.33/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.33/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.33/1.50  --bmc1_ucm_extend_mode                  1
% 7.33/1.50  --bmc1_ucm_init_mode                    2
% 7.33/1.50  --bmc1_ucm_cone_mode                    none
% 7.33/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.33/1.50  --bmc1_ucm_relax_model                  4
% 7.33/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.33/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.33/1.50  --bmc1_ucm_layered_model                none
% 7.33/1.50  --bmc1_ucm_max_lemma_size               10
% 7.33/1.50  
% 7.33/1.50  ------ AIG Options
% 7.33/1.50  
% 7.33/1.50  --aig_mode                              false
% 7.33/1.50  
% 7.33/1.50  ------ Instantiation Options
% 7.33/1.50  
% 7.33/1.50  --instantiation_flag                    true
% 7.33/1.50  --inst_sos_flag                         false
% 7.33/1.50  --inst_sos_phase                        true
% 7.33/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.33/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.33/1.50  --inst_lit_sel_side                     none
% 7.33/1.50  --inst_solver_per_active                1400
% 7.33/1.50  --inst_solver_calls_frac                1.
% 7.33/1.50  --inst_passive_queue_type               priority_queues
% 7.33/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.33/1.50  --inst_passive_queues_freq              [25;2]
% 7.33/1.50  --inst_dismatching                      true
% 7.33/1.50  --inst_eager_unprocessed_to_passive     true
% 7.33/1.50  --inst_prop_sim_given                   true
% 7.33/1.50  --inst_prop_sim_new                     false
% 7.33/1.50  --inst_subs_new                         false
% 7.33/1.50  --inst_eq_res_simp                      false
% 7.33/1.50  --inst_subs_given                       false
% 7.33/1.50  --inst_orphan_elimination               true
% 7.33/1.50  --inst_learning_loop_flag               true
% 7.33/1.50  --inst_learning_start                   3000
% 7.33/1.50  --inst_learning_factor                  2
% 7.33/1.50  --inst_start_prop_sim_after_learn       3
% 7.33/1.50  --inst_sel_renew                        solver
% 7.33/1.50  --inst_lit_activity_flag                true
% 7.33/1.50  --inst_restr_to_given                   false
% 7.33/1.50  --inst_activity_threshold               500
% 7.33/1.50  --inst_out_proof                        true
% 7.33/1.50  
% 7.33/1.50  ------ Resolution Options
% 7.33/1.50  
% 7.33/1.50  --resolution_flag                       false
% 7.33/1.50  --res_lit_sel                           adaptive
% 7.33/1.50  --res_lit_sel_side                      none
% 7.33/1.50  --res_ordering                          kbo
% 7.33/1.50  --res_to_prop_solver                    active
% 7.33/1.50  --res_prop_simpl_new                    false
% 7.33/1.50  --res_prop_simpl_given                  true
% 7.33/1.50  --res_passive_queue_type                priority_queues
% 7.33/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.33/1.50  --res_passive_queues_freq               [15;5]
% 7.33/1.50  --res_forward_subs                      full
% 7.33/1.50  --res_backward_subs                     full
% 7.33/1.50  --res_forward_subs_resolution           true
% 7.33/1.50  --res_backward_subs_resolution          true
% 7.33/1.50  --res_orphan_elimination                true
% 7.33/1.50  --res_time_limit                        2.
% 7.33/1.50  --res_out_proof                         true
% 7.33/1.50  
% 7.33/1.50  ------ Superposition Options
% 7.33/1.50  
% 7.33/1.50  --superposition_flag                    true
% 7.33/1.50  --sup_passive_queue_type                priority_queues
% 7.33/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.33/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.33/1.50  --demod_completeness_check              fast
% 7.33/1.50  --demod_use_ground                      true
% 7.33/1.50  --sup_to_prop_solver                    passive
% 7.33/1.50  --sup_prop_simpl_new                    true
% 7.33/1.50  --sup_prop_simpl_given                  true
% 7.33/1.50  --sup_fun_splitting                     false
% 7.33/1.50  --sup_smt_interval                      50000
% 7.33/1.50  
% 7.33/1.50  ------ Superposition Simplification Setup
% 7.33/1.50  
% 7.33/1.50  --sup_indices_passive                   []
% 7.33/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.33/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.50  --sup_full_bw                           [BwDemod]
% 7.33/1.50  --sup_immed_triv                        [TrivRules]
% 7.33/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.50  --sup_immed_bw_main                     []
% 7.33/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.33/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.33/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.33/1.50  
% 7.33/1.50  ------ Combination Options
% 7.33/1.50  
% 7.33/1.50  --comb_res_mult                         3
% 7.33/1.50  --comb_sup_mult                         2
% 7.33/1.50  --comb_inst_mult                        10
% 7.33/1.50  
% 7.33/1.50  ------ Debug Options
% 7.33/1.50  
% 7.33/1.50  --dbg_backtrace                         false
% 7.33/1.50  --dbg_dump_prop_clauses                 false
% 7.33/1.50  --dbg_dump_prop_clauses_file            -
% 7.33/1.50  --dbg_out_stat                          false
% 7.33/1.50  
% 7.33/1.50  
% 7.33/1.50  
% 7.33/1.50  
% 7.33/1.50  ------ Proving...
% 7.33/1.50  
% 7.33/1.50  
% 7.33/1.50  % SZS status Theorem for theBenchmark.p
% 7.33/1.50  
% 7.33/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.33/1.50  
% 7.33/1.50  fof(f21,conjecture,(
% 7.33/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f22,negated_conjecture,(
% 7.33/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.33/1.50    inference(negated_conjecture,[],[f21])).
% 7.33/1.50  
% 7.33/1.50  fof(f44,plain,(
% 7.33/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.33/1.50    inference(ennf_transformation,[],[f22])).
% 7.33/1.50  
% 7.33/1.50  fof(f45,plain,(
% 7.33/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.33/1.50    inference(flattening,[],[f44])).
% 7.33/1.50  
% 7.33/1.50  fof(f61,plain,(
% 7.33/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.33/1.50    introduced(choice_axiom,[])).
% 7.33/1.50  
% 7.33/1.50  fof(f60,plain,(
% 7.33/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.33/1.50    introduced(choice_axiom,[])).
% 7.33/1.50  
% 7.33/1.50  fof(f59,plain,(
% 7.33/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.33/1.50    introduced(choice_axiom,[])).
% 7.33/1.50  
% 7.33/1.50  fof(f58,plain,(
% 7.33/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.33/1.50    introduced(choice_axiom,[])).
% 7.33/1.50  
% 7.33/1.50  fof(f57,plain,(
% 7.33/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.33/1.50    introduced(choice_axiom,[])).
% 7.33/1.50  
% 7.33/1.50  fof(f56,plain,(
% 7.33/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.33/1.50    introduced(choice_axiom,[])).
% 7.33/1.50  
% 7.33/1.50  fof(f62,plain,(
% 7.33/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.33/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f61,f60,f59,f58,f57,f56])).
% 7.33/1.50  
% 7.33/1.50  fof(f100,plain,(
% 7.33/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f8,axiom,(
% 7.33/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f51,plain,(
% 7.33/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.33/1.50    inference(nnf_transformation,[],[f8])).
% 7.33/1.50  
% 7.33/1.50  fof(f75,plain,(
% 7.33/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.33/1.50    inference(cnf_transformation,[],[f51])).
% 7.33/1.50  
% 7.33/1.50  fof(f7,axiom,(
% 7.33/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f26,plain,(
% 7.33/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.33/1.50    inference(ennf_transformation,[],[f7])).
% 7.33/1.50  
% 7.33/1.50  fof(f74,plain,(
% 7.33/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.33/1.50    inference(cnf_transformation,[],[f26])).
% 7.33/1.50  
% 7.33/1.50  fof(f76,plain,(
% 7.33/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f51])).
% 7.33/1.50  
% 7.33/1.50  fof(f104,plain,(
% 7.33/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f18,axiom,(
% 7.33/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f38,plain,(
% 7.33/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.33/1.50    inference(ennf_transformation,[],[f18])).
% 7.33/1.50  
% 7.33/1.50  fof(f39,plain,(
% 7.33/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.33/1.50    inference(flattening,[],[f38])).
% 7.33/1.50  
% 7.33/1.50  fof(f88,plain,(
% 7.33/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f39])).
% 7.33/1.50  
% 7.33/1.50  fof(f102,plain,(
% 7.33/1.50    v1_funct_1(sK4)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f107,plain,(
% 7.33/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f105,plain,(
% 7.33/1.50    v1_funct_1(sK5)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f19,axiom,(
% 7.33/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f40,plain,(
% 7.33/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.33/1.50    inference(ennf_transformation,[],[f19])).
% 7.33/1.50  
% 7.33/1.50  fof(f41,plain,(
% 7.33/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.33/1.50    inference(flattening,[],[f40])).
% 7.33/1.50  
% 7.33/1.50  fof(f54,plain,(
% 7.33/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.33/1.50    inference(nnf_transformation,[],[f41])).
% 7.33/1.50  
% 7.33/1.50  fof(f55,plain,(
% 7.33/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.33/1.50    inference(flattening,[],[f54])).
% 7.33/1.50  
% 7.33/1.50  fof(f90,plain,(
% 7.33/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f55])).
% 7.33/1.50  
% 7.33/1.50  fof(f115,plain,(
% 7.33/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.50    inference(equality_resolution,[],[f90])).
% 7.33/1.50  
% 7.33/1.50  fof(f20,axiom,(
% 7.33/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f42,plain,(
% 7.33/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.33/1.50    inference(ennf_transformation,[],[f20])).
% 7.33/1.50  
% 7.33/1.50  fof(f43,plain,(
% 7.33/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.33/1.50    inference(flattening,[],[f42])).
% 7.33/1.50  
% 7.33/1.50  fof(f92,plain,(
% 7.33/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f43])).
% 7.33/1.50  
% 7.33/1.50  fof(f93,plain,(
% 7.33/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f43])).
% 7.33/1.50  
% 7.33/1.50  fof(f94,plain,(
% 7.33/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f43])).
% 7.33/1.50  
% 7.33/1.50  fof(f96,plain,(
% 7.33/1.50    ~v1_xboole_0(sK1)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f99,plain,(
% 7.33/1.50    ~v1_xboole_0(sK3)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f106,plain,(
% 7.33/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f97,plain,(
% 7.33/1.50    ~v1_xboole_0(sK2)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f103,plain,(
% 7.33/1.50    v1_funct_2(sK4,sK2,sK1)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f15,axiom,(
% 7.33/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f34,plain,(
% 7.33/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.33/1.50    inference(ennf_transformation,[],[f15])).
% 7.33/1.50  
% 7.33/1.50  fof(f35,plain,(
% 7.33/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.33/1.50    inference(flattening,[],[f34])).
% 7.33/1.50  
% 7.33/1.50  fof(f53,plain,(
% 7.33/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.33/1.50    inference(nnf_transformation,[],[f35])).
% 7.33/1.50  
% 7.33/1.50  fof(f84,plain,(
% 7.33/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f53])).
% 7.33/1.50  
% 7.33/1.50  fof(f101,plain,(
% 7.33/1.50    r1_subset_1(sK2,sK3)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f2,axiom,(
% 7.33/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f46,plain,(
% 7.33/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.33/1.50    inference(nnf_transformation,[],[f2])).
% 7.33/1.50  
% 7.33/1.50  fof(f64,plain,(
% 7.33/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f46])).
% 7.33/1.50  
% 7.33/1.50  fof(f16,axiom,(
% 7.33/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f36,plain,(
% 7.33/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.33/1.50    inference(ennf_transformation,[],[f16])).
% 7.33/1.50  
% 7.33/1.50  fof(f86,plain,(
% 7.33/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.33/1.50    inference(cnf_transformation,[],[f36])).
% 7.33/1.50  
% 7.33/1.50  fof(f11,axiom,(
% 7.33/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f28,plain,(
% 7.33/1.50    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.33/1.50    inference(ennf_transformation,[],[f11])).
% 7.33/1.50  
% 7.33/1.50  fof(f29,plain,(
% 7.33/1.50    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.33/1.50    inference(flattening,[],[f28])).
% 7.33/1.50  
% 7.33/1.50  fof(f79,plain,(
% 7.33/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f29])).
% 7.33/1.50  
% 7.33/1.50  fof(f17,axiom,(
% 7.33/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f23,plain,(
% 7.33/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.33/1.50    inference(pure_predicate_removal,[],[f17])).
% 7.33/1.50  
% 7.33/1.50  fof(f37,plain,(
% 7.33/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.33/1.50    inference(ennf_transformation,[],[f23])).
% 7.33/1.50  
% 7.33/1.50  fof(f87,plain,(
% 7.33/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.33/1.50    inference(cnf_transformation,[],[f37])).
% 7.33/1.50  
% 7.33/1.50  fof(f12,axiom,(
% 7.33/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f30,plain,(
% 7.33/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.33/1.50    inference(ennf_transformation,[],[f12])).
% 7.33/1.50  
% 7.33/1.50  fof(f31,plain,(
% 7.33/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.33/1.50    inference(flattening,[],[f30])).
% 7.33/1.50  
% 7.33/1.50  fof(f80,plain,(
% 7.33/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f31])).
% 7.33/1.50  
% 7.33/1.50  fof(f14,axiom,(
% 7.33/1.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f33,plain,(
% 7.33/1.50    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.33/1.50    inference(ennf_transformation,[],[f14])).
% 7.33/1.50  
% 7.33/1.50  fof(f52,plain,(
% 7.33/1.50    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.33/1.50    inference(nnf_transformation,[],[f33])).
% 7.33/1.50  
% 7.33/1.50  fof(f82,plain,(
% 7.33/1.50    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f52])).
% 7.33/1.50  
% 7.33/1.50  fof(f13,axiom,(
% 7.33/1.50    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f32,plain,(
% 7.33/1.50    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.33/1.50    inference(ennf_transformation,[],[f13])).
% 7.33/1.50  
% 7.33/1.50  fof(f81,plain,(
% 7.33/1.50    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f32])).
% 7.33/1.50  
% 7.33/1.50  fof(f4,axiom,(
% 7.33/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f47,plain,(
% 7.33/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.33/1.50    inference(nnf_transformation,[],[f4])).
% 7.33/1.50  
% 7.33/1.50  fof(f48,plain,(
% 7.33/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.33/1.50    inference(flattening,[],[f47])).
% 7.33/1.50  
% 7.33/1.50  fof(f67,plain,(
% 7.33/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.33/1.50    inference(cnf_transformation,[],[f48])).
% 7.33/1.50  
% 7.33/1.50  fof(f110,plain,(
% 7.33/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.33/1.50    inference(equality_resolution,[],[f67])).
% 7.33/1.50  
% 7.33/1.50  fof(f5,axiom,(
% 7.33/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f49,plain,(
% 7.33/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.33/1.50    inference(nnf_transformation,[],[f5])).
% 7.33/1.50  
% 7.33/1.50  fof(f50,plain,(
% 7.33/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.33/1.50    inference(flattening,[],[f49])).
% 7.33/1.50  
% 7.33/1.50  fof(f72,plain,(
% 7.33/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.33/1.50    inference(cnf_transformation,[],[f50])).
% 7.33/1.50  
% 7.33/1.50  fof(f111,plain,(
% 7.33/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.33/1.50    inference(equality_resolution,[],[f72])).
% 7.33/1.50  
% 7.33/1.50  fof(f9,axiom,(
% 7.33/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f77,plain,(
% 7.33/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.33/1.50    inference(cnf_transformation,[],[f9])).
% 7.33/1.50  
% 7.33/1.50  fof(f70,plain,(
% 7.33/1.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f50])).
% 7.33/1.50  
% 7.33/1.50  fof(f71,plain,(
% 7.33/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.33/1.50    inference(cnf_transformation,[],[f50])).
% 7.33/1.50  
% 7.33/1.50  fof(f112,plain,(
% 7.33/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.33/1.50    inference(equality_resolution,[],[f71])).
% 7.33/1.50  
% 7.33/1.50  fof(f3,axiom,(
% 7.33/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.33/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.33/1.50  
% 7.33/1.50  fof(f24,plain,(
% 7.33/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.33/1.50    inference(ennf_transformation,[],[f3])).
% 7.33/1.50  
% 7.33/1.50  fof(f66,plain,(
% 7.33/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f24])).
% 7.33/1.50  
% 7.33/1.50  fof(f83,plain,(
% 7.33/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f52])).
% 7.33/1.50  
% 7.33/1.50  fof(f89,plain,(
% 7.33/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.50    inference(cnf_transformation,[],[f55])).
% 7.33/1.50  
% 7.33/1.50  fof(f116,plain,(
% 7.33/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.33/1.50    inference(equality_resolution,[],[f89])).
% 7.33/1.50  
% 7.33/1.50  fof(f108,plain,(
% 7.33/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f98,plain,(
% 7.33/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  fof(f95,plain,(
% 7.33/1.50    ~v1_xboole_0(sK0)),
% 7.33/1.50    inference(cnf_transformation,[],[f62])).
% 7.33/1.50  
% 7.33/1.50  cnf(c_40,negated_conjecture,
% 7.33/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.33/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2127,plain,
% 7.33/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_13,plain,
% 7.33/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2146,plain,
% 7.33/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.33/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_3732,plain,
% 7.33/1.50      ( r1_tarski(sK3,sK0) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2127,c_2146]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_11,plain,
% 7.33/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.33/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.33/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_12,plain,
% 7.33/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_329,plain,
% 7.33/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.33/1.50      inference(prop_impl,[status(thm)],[c_12]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_330,plain,
% 7.33/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.33/1.50      inference(renaming,[status(thm)],[c_329]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_421,plain,
% 7.33/1.50      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.33/1.50      inference(bin_hyper_res,[status(thm)],[c_11,c_330]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2118,plain,
% 7.33/1.50      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 7.33/1.50      | r1_tarski(X2,X0) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_17336,plain,
% 7.33/1.50      ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_3732,c_2118]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_36,negated_conjecture,
% 7.33/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.33/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2130,plain,
% 7.33/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_25,plain,
% 7.33/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.33/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2138,plain,
% 7.33/1.50      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.33/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.33/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_6428,plain,
% 7.33/1.50      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 7.33/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2130,c_2138]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_38,negated_conjecture,
% 7.33/1.50      ( v1_funct_1(sK4) ),
% 7.33/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2623,plain,
% 7.33/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.33/1.50      | ~ v1_funct_1(sK4)
% 7.33/1.50      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_25]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2835,plain,
% 7.33/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.33/1.50      | ~ v1_funct_1(sK4)
% 7.33/1.50      | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_2623]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7139,plain,
% 7.33/1.50      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_6428,c_38,c_36,c_2835]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_33,negated_conjecture,
% 7.33/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.33/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2133,plain,
% 7.33/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_6427,plain,
% 7.33/1.50      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 7.33/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2133,c_2138]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_35,negated_conjecture,
% 7.33/1.50      ( v1_funct_1(sK5) ),
% 7.33/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2618,plain,
% 7.33/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.33/1.50      | ~ v1_funct_1(sK5)
% 7.33/1.50      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_25]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2829,plain,
% 7.33/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.33/1.50      | ~ v1_funct_1(sK5)
% 7.33/1.50      | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_2618]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_6824,plain,
% 7.33/1.50      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_6427,c_35,c_33,c_2829]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_27,plain,
% 7.33/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_1(X3)
% 7.33/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X1)
% 7.33/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f115]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_31,plain,
% 7.33/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_1(X3)
% 7.33/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_30,plain,
% 7.33/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_1(X3)
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_29,plain,
% 7.33/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_1(X3)
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_246,plain,
% 7.33/1.50      ( ~ v1_funct_1(X3)
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X1)
% 7.33/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_27,c_31,c_30,c_29]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_247,plain,
% 7.33/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_1(X3)
% 7.33/1.50      | v1_xboole_0(X1)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.33/1.50      inference(renaming,[status(thm)],[c_246]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2120,plain,
% 7.33/1.50      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 7.33/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.33/1.50      | v1_funct_2(X5,X4,X1) != iProver_top
% 7.33/1.50      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 7.33/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.33/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 7.33/1.50      | v1_funct_1(X2) != iProver_top
% 7.33/1.50      | v1_funct_1(X5) != iProver_top
% 7.33/1.50      | v1_xboole_0(X3) = iProver_top
% 7.33/1.50      | v1_xboole_0(X1) = iProver_top
% 7.33/1.50      | v1_xboole_0(X4) = iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_6830,plain,
% 7.33/1.50      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 7.33/1.50      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.33/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.33/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | v1_funct_1(X1) != iProver_top
% 7.33/1.50      | v1_funct_1(sK5) != iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top
% 7.33/1.50      | v1_xboole_0(X2) = iProver_top
% 7.33/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.33/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_6824,c_2120]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_44,negated_conjecture,
% 7.33/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_47,plain,
% 7.33/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_41,negated_conjecture,
% 7.33/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.33/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_50,plain,
% 7.33/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_56,plain,
% 7.33/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_34,negated_conjecture,
% 7.33/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_57,plain,
% 7.33/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_58,plain,
% 7.33/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7850,plain,
% 7.33/1.50      ( v1_funct_1(X1) != iProver_top
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.33/1.50      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 7.33/1.50      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top
% 7.33/1.50      | v1_xboole_0(X2) = iProver_top ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_6830,c_47,c_50,c_56,c_57,c_58]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7851,plain,
% 7.33/1.50      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 7.33/1.50      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | v1_funct_1(X1) != iProver_top
% 7.33/1.50      | v1_xboole_0(X2) = iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.33/1.50      inference(renaming,[status(thm)],[c_7850]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7866,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.33/1.50      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.33/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.33/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | v1_funct_1(sK4) != iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top
% 7.33/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_7139,c_7851]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_43,negated_conjecture,
% 7.33/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.33/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_48,plain,
% 7.33/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_53,plain,
% 7.33/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_37,negated_conjecture,
% 7.33/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_54,plain,
% 7.33/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_55,plain,
% 7.33/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7889,plain,
% 7.33/1.50      ( v1_xboole_0(X0) = iProver_top
% 7.33/1.50      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.33/1.50      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_7866,c_48,c_53,c_54,c_55]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7890,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.33/1.50      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.33/1.50      inference(renaming,[status(thm)],[c_7889]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_17927,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.33/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_17336,c_7890]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_22,plain,
% 7.33/1.50      ( ~ r1_subset_1(X0,X1)
% 7.33/1.50      | r1_xboole_0(X0,X1)
% 7.33/1.50      | v1_xboole_0(X0)
% 7.33/1.50      | v1_xboole_0(X1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_39,negated_conjecture,
% 7.33/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.33/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_588,plain,
% 7.33/1.50      ( r1_xboole_0(X0,X1)
% 7.33/1.50      | v1_xboole_0(X0)
% 7.33/1.50      | v1_xboole_0(X1)
% 7.33/1.50      | sK3 != X1
% 7.33/1.50      | sK2 != X0 ),
% 7.33/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_39]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_589,plain,
% 7.33/1.50      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.33/1.50      inference(unflattening,[status(thm)],[c_588]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_591,plain,
% 7.33/1.50      ( r1_xboole_0(sK2,sK3) ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_589,c_43,c_41]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2116,plain,
% 7.33/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2,plain,
% 7.33/1.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2151,plain,
% 7.33/1.50      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 7.33/1.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_3388,plain,
% 7.33/1.50      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2116,c_2151]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_23,plain,
% 7.33/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | v1_relat_1(X0) ),
% 7.33/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2139,plain,
% 7.33/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.33/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_3918,plain,
% 7.33/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2133,c_2139]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_3919,plain,
% 7.33/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2130,c_2139]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_16,plain,
% 7.33/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.33/1.50      | ~ v1_relat_1(X2)
% 7.33/1.50      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2143,plain,
% 7.33/1.50      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 7.33/1.50      | r1_xboole_0(X1,X2) != iProver_top
% 7.33/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_5655,plain,
% 7.33/1.50      ( k7_relat_1(k7_relat_1(X0,sK2),sK3) = k1_xboole_0
% 7.33/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2116,c_2143]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_5736,plain,
% 7.33/1.50      ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_3919,c_5655]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_24,plain,
% 7.33/1.50      ( v4_relat_1(X0,X1)
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.33/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_17,plain,
% 7.33/1.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_567,plain,
% 7.33/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ v1_relat_1(X0)
% 7.33/1.50      | k7_relat_1(X0,X1) = X0 ),
% 7.33/1.50      inference(resolution,[status(thm)],[c_24,c_17]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_571,plain,
% 7.33/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | k7_relat_1(X0,X1) = X0 ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_567,c_24,c_23,c_17]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2117,plain,
% 7.33/1.50      ( k7_relat_1(X0,X1) = X0
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_3312,plain,
% 7.33/1.50      ( k7_relat_1(sK4,sK2) = sK4 ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2130,c_2117]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_5738,plain,
% 7.33/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.33/1.50      inference(light_normalisation,[status(thm)],[c_5736,c_3312]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_20,plain,
% 7.33/1.50      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.33/1.50      | ~ v1_relat_1(X0)
% 7.33/1.50      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2140,plain,
% 7.33/1.50      ( k7_relat_1(X0,X1) != k1_xboole_0
% 7.33/1.50      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 7.33/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_5748,plain,
% 7.33/1.50      ( r1_xboole_0(k1_relat_1(sK4),sK3) = iProver_top
% 7.33/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_5738,c_2140]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2545,plain,
% 7.33/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.33/1.50      | v1_relat_1(sK4) ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_23]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2546,plain,
% 7.33/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.33/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_2545]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_5904,plain,
% 7.33/1.50      ( r1_xboole_0(k1_relat_1(sK4),sK3) = iProver_top ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_5748,c_55,c_2546]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_5909,plain,
% 7.33/1.50      ( k3_xboole_0(k1_relat_1(sK4),sK3) = k1_xboole_0 ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_5904,c_2151]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18,plain,
% 7.33/1.50      ( ~ v1_relat_1(X0)
% 7.33/1.50      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 7.33/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2142,plain,
% 7.33/1.50      ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
% 7.33/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_4537,plain,
% 7.33/1.50      ( k1_relat_1(k7_relat_1(sK4,X0)) = k3_xboole_0(k1_relat_1(sK4),X0) ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_3919,c_2142]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7702,plain,
% 7.33/1.50      ( k1_relat_1(k7_relat_1(sK4,sK3)) = k1_xboole_0 ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_5909,c_4537]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7704,plain,
% 7.33/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.33/1.50      inference(light_normalisation,[status(thm)],[c_7702,c_5738]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_6,plain,
% 7.33/1.50      ( r1_tarski(X0,X0) ),
% 7.33/1.50      inference(cnf_transformation,[],[f110]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2148,plain,
% 7.33/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2147,plain,
% 7.33/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.33/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7,plain,
% 7.33/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f111]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_3313,plain,
% 7.33/1.50      ( k7_relat_1(X0,X1) = X0
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_7,c_2117]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_3862,plain,
% 7.33/1.50      ( k7_relat_1(X0,X1) = X0
% 7.33/1.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2147,c_3313]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_4370,plain,
% 7.33/1.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_2148,c_3862]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_4648,plain,
% 7.33/1.50      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 7.33/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_4370,c_2140]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_14,plain,
% 7.33/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.33/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_108,plain,
% 7.33/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_110,plain,
% 7.33/1.50      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_108]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_9,plain,
% 7.33/1.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.33/1.50      | k1_xboole_0 = X1
% 7.33/1.50      | k1_xboole_0 = X0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_123,plain,
% 7.33/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.33/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_8,plain,
% 7.33/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_124,plain,
% 7.33/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_1224,plain,
% 7.33/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.33/1.50      theory(equality) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2641,plain,
% 7.33/1.50      ( v1_relat_1(X0)
% 7.33/1.50      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 7.33/1.50      | X0 != k2_zfmisc_1(X1,X2) ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_1224]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2642,plain,
% 7.33/1.50      ( X0 != k2_zfmisc_1(X1,X2)
% 7.33/1.50      | v1_relat_1(X0) = iProver_top
% 7.33/1.50      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_2641]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2644,plain,
% 7.33/1.50      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.33/1.50      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.33/1.50      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_2642]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_1217,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2986,plain,
% 7.33/1.50      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_1217]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2987,plain,
% 7.33/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.33/1.50      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.33/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.33/1.50      inference(instantiation,[status(thm)],[c_2986]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_9563,plain,
% 7.33/1.50      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_4648,c_110,c_123,c_124,c_2644,c_2987]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_3,plain,
% 7.33/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.33/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2150,plain,
% 7.33/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.33/1.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_9571,plain,
% 7.33/1.50      ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_9563,c_2150]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_10865,plain,
% 7.33/1.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.33/1.50      inference(demodulation,[status(thm)],[c_7704,c_9571]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_19,plain,
% 7.33/1.50      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.33/1.50      | ~ v1_relat_1(X0)
% 7.33/1.50      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.33/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2141,plain,
% 7.33/1.50      ( k7_relat_1(X0,X1) = k1_xboole_0
% 7.33/1.50      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 7.33/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_12070,plain,
% 7.33/1.50      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.33/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_10865,c_2141]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_13210,plain,
% 7.33/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_3918,c_12070]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18067,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.33/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(light_normalisation,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_17927,c_3388,c_13210]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18068,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.33/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(demodulation,[status(thm)],[c_18067,c_17336]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_13211,plain,
% 7.33/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_3919,c_12070]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18069,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.33/1.50      | k1_xboole_0 != k1_xboole_0
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(light_normalisation,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_18068,c_3388,c_13211]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18070,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(equality_resolution_simp,[status(thm)],[c_18069]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_28,plain,
% 7.33/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_1(X3)
% 7.33/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X1)
% 7.33/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.33/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_239,plain,
% 7.33/1.50      ( ~ v1_funct_1(X3)
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X1)
% 7.33/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_28,c_31,c_30,c_29]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_240,plain,
% 7.33/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.33/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.33/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.33/1.50      | ~ v1_funct_1(X0)
% 7.33/1.50      | ~ v1_funct_1(X3)
% 7.33/1.50      | v1_xboole_0(X1)
% 7.33/1.50      | v1_xboole_0(X2)
% 7.33/1.50      | v1_xboole_0(X4)
% 7.33/1.50      | v1_xboole_0(X5)
% 7.33/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.33/1.50      inference(renaming,[status(thm)],[c_239]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_2121,plain,
% 7.33/1.50      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 7.33/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.33/1.50      | v1_funct_2(X5,X4,X1) != iProver_top
% 7.33/1.50      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 7.33/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.33/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 7.33/1.50      | v1_funct_1(X2) != iProver_top
% 7.33/1.50      | v1_funct_1(X5) != iProver_top
% 7.33/1.50      | v1_xboole_0(X3) = iProver_top
% 7.33/1.50      | v1_xboole_0(X1) = iProver_top
% 7.33/1.50      | v1_xboole_0(X4) = iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_240]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_6829,plain,
% 7.33/1.50      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 7.33/1.50      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.33/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.33/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | v1_funct_1(X1) != iProver_top
% 7.33/1.50      | v1_funct_1(sK5) != iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top
% 7.33/1.50      | v1_xboole_0(X2) = iProver_top
% 7.33/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.33/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_6824,c_2121]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7363,plain,
% 7.33/1.50      ( v1_funct_1(X1) != iProver_top
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.33/1.50      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 7.33/1.50      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top
% 7.33/1.50      | v1_xboole_0(X2) = iProver_top ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_6829,c_47,c_50,c_56,c_57,c_58]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7364,plain,
% 7.33/1.50      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.33/1.50      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 7.33/1.50      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.33/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.33/1.50      | v1_funct_1(X1) != iProver_top
% 7.33/1.50      | v1_xboole_0(X2) = iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.33/1.50      inference(renaming,[status(thm)],[c_7363]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7379,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.33/1.50      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.33/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.33/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | v1_funct_1(sK4) != iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top
% 7.33/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_7139,c_7364]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7481,plain,
% 7.33/1.50      ( v1_xboole_0(X0) = iProver_top
% 7.33/1.50      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.33/1.50      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.33/1.50      inference(global_propositional_subsumption,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_7379,c_48,c_53,c_54,c_55]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7482,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.33/1.50      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.33/1.50      inference(renaming,[status(thm)],[c_7481]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_17928,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.33/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(superposition,[status(thm)],[c_17336,c_7482]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18054,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.33/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(light_normalisation,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_17928,c_3388,c_13210]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18055,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.33/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(demodulation,[status(thm)],[c_18054,c_17336]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18056,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.33/1.50      | k1_xboole_0 != k1_xboole_0
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(light_normalisation,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_18055,c_3388,c_13211]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_18057,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.33/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.33/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.33/1.50      inference(equality_resolution_simp,[status(thm)],[c_18056]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_32,negated_conjecture,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.33/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.33/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.33/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_6828,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.33/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.33/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.33/1.50      inference(demodulation,[status(thm)],[c_6824,c_32]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_7143,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.33/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.33/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.33/1.50      inference(demodulation,[status(thm)],[c_7139,c_6828]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_17918,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.33/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.33/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.33/1.50      inference(demodulation,[status(thm)],[c_17336,c_7143]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_17919,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.33/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.33/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.33/1.50      inference(light_normalisation,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_17918,c_3388,c_13210,c_13211]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_17920,plain,
% 7.33/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.33/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.33/1.50      inference(equality_resolution_simp,[status(thm)],[c_17919]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_51,plain,
% 7.33/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_42,negated_conjecture,
% 7.33/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.33/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_49,plain,
% 7.33/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_45,negated_conjecture,
% 7.33/1.50      ( ~ v1_xboole_0(sK0) ),
% 7.33/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(c_46,plain,
% 7.33/1.50      ( v1_xboole_0(sK0) != iProver_top ),
% 7.33/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.33/1.50  
% 7.33/1.50  cnf(contradiction,plain,
% 7.33/1.50      ( $false ),
% 7.33/1.50      inference(minisat,
% 7.33/1.50                [status(thm)],
% 7.33/1.50                [c_18070,c_18057,c_17920,c_51,c_49,c_46]) ).
% 7.33/1.50  
% 7.33/1.50  
% 7.33/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.33/1.50  
% 7.33/1.50  ------                               Statistics
% 7.33/1.50  
% 7.33/1.50  ------ General
% 7.33/1.50  
% 7.33/1.50  abstr_ref_over_cycles:                  0
% 7.33/1.50  abstr_ref_under_cycles:                 0
% 7.33/1.50  gc_basic_clause_elim:                   0
% 7.33/1.50  forced_gc_time:                         0
% 7.33/1.50  parsing_time:                           0.011
% 7.33/1.50  unif_index_cands_time:                  0.
% 7.33/1.50  unif_index_add_time:                    0.
% 7.33/1.50  orderings_time:                         0.
% 7.33/1.50  out_proof_time:                         0.018
% 7.33/1.50  total_time:                             0.736
% 7.33/1.50  num_of_symbols:                         56
% 7.33/1.50  num_of_terms:                           24250
% 7.33/1.50  
% 7.33/1.50  ------ Preprocessing
% 7.33/1.50  
% 7.33/1.50  num_of_splits:                          0
% 7.33/1.50  num_of_split_atoms:                     0
% 7.33/1.50  num_of_reused_defs:                     0
% 7.33/1.50  num_eq_ax_congr_red:                    14
% 7.33/1.50  num_of_sem_filtered_clauses:            1
% 7.33/1.50  num_of_subtypes:                        0
% 7.33/1.50  monotx_restored_types:                  0
% 7.33/1.50  sat_num_of_epr_types:                   0
% 7.33/1.50  sat_num_of_non_cyclic_types:            0
% 7.33/1.50  sat_guarded_non_collapsed_types:        0
% 7.33/1.50  num_pure_diseq_elim:                    0
% 7.33/1.50  simp_replaced_by:                       0
% 7.33/1.50  res_preprocessed:                       206
% 7.33/1.50  prep_upred:                             0
% 7.33/1.50  prep_unflattend:                        16
% 7.33/1.50  smt_new_axioms:                         0
% 7.33/1.50  pred_elim_cands:                        7
% 7.33/1.50  pred_elim:                              2
% 7.33/1.50  pred_elim_cl:                           3
% 7.33/1.50  pred_elim_cycles:                       4
% 7.33/1.50  merged_defs:                            16
% 7.33/1.50  merged_defs_ncl:                        0
% 7.33/1.50  bin_hyper_res:                          18
% 7.33/1.50  prep_cycles:                            4
% 7.33/1.50  pred_elim_time:                         0.006
% 7.33/1.50  splitting_time:                         0.
% 7.33/1.50  sem_filter_time:                        0.
% 7.33/1.50  monotx_time:                            0.001
% 7.33/1.50  subtype_inf_time:                       0.
% 7.33/1.50  
% 7.33/1.50  ------ Problem properties
% 7.33/1.50  
% 7.33/1.50  clauses:                                42
% 7.33/1.50  conjectures:                            13
% 7.33/1.50  epr:                                    12
% 7.33/1.50  horn:                                   35
% 7.33/1.50  ground:                                 14
% 7.33/1.50  unary:                                  18
% 7.33/1.50  binary:                                 10
% 7.33/1.50  lits:                                   146
% 7.33/1.50  lits_eq:                                27
% 7.33/1.50  fd_pure:                                0
% 7.33/1.50  fd_pseudo:                              0
% 7.33/1.50  fd_cond:                                1
% 7.33/1.50  fd_pseudo_cond:                         1
% 7.33/1.50  ac_symbols:                             0
% 7.33/1.50  
% 7.33/1.50  ------ Propositional Solver
% 7.33/1.50  
% 7.33/1.50  prop_solver_calls:                      28
% 7.33/1.50  prop_fast_solver_calls:                 2245
% 7.33/1.50  smt_solver_calls:                       0
% 7.33/1.50  smt_fast_solver_calls:                  0
% 7.33/1.50  prop_num_of_clauses:                    7517
% 7.33/1.50  prop_preprocess_simplified:             18579
% 7.33/1.50  prop_fo_subsumed:                       90
% 7.33/1.50  prop_solver_time:                       0.
% 7.33/1.50  smt_solver_time:                        0.
% 7.33/1.50  smt_fast_solver_time:                   0.
% 7.33/1.50  prop_fast_solver_time:                  0.
% 7.33/1.50  prop_unsat_core_time:                   0.001
% 7.33/1.50  
% 7.33/1.50  ------ QBF
% 7.33/1.50  
% 7.33/1.50  qbf_q_res:                              0
% 7.33/1.50  qbf_num_tautologies:                    0
% 7.33/1.50  qbf_prep_cycles:                        0
% 7.33/1.50  
% 7.33/1.50  ------ BMC1
% 7.33/1.50  
% 7.33/1.50  bmc1_current_bound:                     -1
% 7.33/1.50  bmc1_last_solved_bound:                 -1
% 7.33/1.50  bmc1_unsat_core_size:                   -1
% 7.33/1.50  bmc1_unsat_core_parents_size:           -1
% 7.33/1.50  bmc1_merge_next_fun:                    0
% 7.33/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.33/1.50  
% 7.33/1.50  ------ Instantiation
% 7.33/1.50  
% 7.33/1.50  inst_num_of_clauses:                    2279
% 7.33/1.50  inst_num_in_passive:                    1197
% 7.33/1.50  inst_num_in_active:                     921
% 7.33/1.50  inst_num_in_unprocessed:                162
% 7.33/1.50  inst_num_of_loops:                      960
% 7.33/1.50  inst_num_of_learning_restarts:          0
% 7.33/1.50  inst_num_moves_active_passive:          37
% 7.33/1.50  inst_lit_activity:                      0
% 7.33/1.50  inst_lit_activity_moves:                0
% 7.33/1.50  inst_num_tautologies:                   0
% 7.33/1.50  inst_num_prop_implied:                  0
% 7.33/1.50  inst_num_existing_simplified:           0
% 7.33/1.50  inst_num_eq_res_simplified:             0
% 7.33/1.50  inst_num_child_elim:                    0
% 7.33/1.50  inst_num_of_dismatching_blockings:      548
% 7.33/1.50  inst_num_of_non_proper_insts:           2190
% 7.33/1.50  inst_num_of_duplicates:                 0
% 7.33/1.50  inst_inst_num_from_inst_to_res:         0
% 7.33/1.50  inst_dismatching_checking_time:         0.
% 7.33/1.50  
% 7.33/1.50  ------ Resolution
% 7.33/1.50  
% 7.33/1.50  res_num_of_clauses:                     0
% 7.33/1.50  res_num_in_passive:                     0
% 7.33/1.50  res_num_in_active:                      0
% 7.33/1.50  res_num_of_loops:                       210
% 7.33/1.50  res_forward_subset_subsumed:            53
% 7.33/1.50  res_backward_subset_subsumed:           4
% 7.33/1.50  res_forward_subsumed:                   0
% 7.33/1.50  res_backward_subsumed:                  0
% 7.33/1.50  res_forward_subsumption_resolution:     0
% 7.33/1.50  res_backward_subsumption_resolution:    0
% 7.33/1.50  res_clause_to_clause_subsumption:       857
% 7.33/1.50  res_orphan_elimination:                 0
% 7.33/1.50  res_tautology_del:                      126
% 7.33/1.50  res_num_eq_res_simplified:              0
% 7.33/1.50  res_num_sel_changes:                    0
% 7.33/1.50  res_moves_from_active_to_pass:          0
% 7.33/1.50  
% 7.33/1.50  ------ Superposition
% 7.33/1.50  
% 7.33/1.50  sup_time_total:                         0.
% 7.33/1.50  sup_time_generating:                    0.
% 7.33/1.50  sup_time_sim_full:                      0.
% 7.33/1.50  sup_time_sim_immed:                     0.
% 7.33/1.50  
% 7.33/1.50  sup_num_of_clauses:                     281
% 7.33/1.50  sup_num_in_active:                      173
% 7.33/1.50  sup_num_in_passive:                     108
% 7.33/1.50  sup_num_of_loops:                       191
% 7.33/1.50  sup_fw_superposition:                   269
% 7.33/1.50  sup_bw_superposition:                   254
% 7.33/1.50  sup_immediate_simplified:               132
% 7.33/1.50  sup_given_eliminated:                   0
% 7.33/1.50  comparisons_done:                       0
% 7.33/1.50  comparisons_avoided:                    0
% 7.33/1.50  
% 7.33/1.50  ------ Simplifications
% 7.33/1.50  
% 7.33/1.50  
% 7.33/1.50  sim_fw_subset_subsumed:                 21
% 7.33/1.50  sim_bw_subset_subsumed:                 0
% 7.33/1.50  sim_fw_subsumed:                        38
% 7.33/1.50  sim_bw_subsumed:                        3
% 7.33/1.50  sim_fw_subsumption_res:                 1
% 7.33/1.50  sim_bw_subsumption_res:                 0
% 7.33/1.50  sim_tautology_del:                      1
% 7.33/1.50  sim_eq_tautology_del:                   26
% 7.33/1.50  sim_eq_res_simp:                        15
% 7.33/1.50  sim_fw_demodulated:                     51
% 7.33/1.50  sim_bw_demodulated:                     19
% 7.33/1.50  sim_light_normalised:                   74
% 7.33/1.50  sim_joinable_taut:                      0
% 7.33/1.50  sim_joinable_simp:                      0
% 7.33/1.50  sim_ac_normalised:                      0
% 7.33/1.50  sim_smt_subsumption:                    0
% 7.33/1.50  
%------------------------------------------------------------------------------
