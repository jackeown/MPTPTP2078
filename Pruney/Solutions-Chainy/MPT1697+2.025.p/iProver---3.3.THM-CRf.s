%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:27 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  245 (3323 expanded)
%              Number of clauses        :  161 ( 866 expanded)
%              Number of leaves         :   22 (1177 expanded)
%              Depth                    :   26
%              Number of atoms          : 1385 (37380 expanded)
%              Number of equality atoms :  595 (8766 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f36])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f48,f47,f46,f45,f44,f43])).

fof(f85,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f32])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f68])).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f34])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f86,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_910,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1436,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_916,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1431,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_2563,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_1431])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1889,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_55,X1_55,sK5,X2_55) = k7_relat_1(sK5,X2_55) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_2115,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
    inference(instantiation,[status(thm)],[c_1889])).

cnf(c_2997,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2563,c_25,c_23,c_2115])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_904,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1442,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | k9_subset_1(X1_55,X2_55,X0_55) = k1_setfam_1(k2_tarski(X2_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1428,plain,
    ( k9_subset_1(X0_55,X1_55,X2_55) = k1_setfam_1(k2_tarski(X1_55,X2_55))
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_2457,plain,
    ( k9_subset_1(sK0,X0_55,sK3) = k1_setfam_1(k2_tarski(X0_55,sK3)) ),
    inference(superposition,[status(thm)],[c_1442,c_1428])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_907,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1439,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_2564,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1431])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1894,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_55,X1_55,sK4,X2_55) = k7_relat_1(sK4,X2_55) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_2120,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_3002,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2564,c_28,c_26,c_2120])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f70])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f71])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f72])).

cnf(c_199,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_21,c_20,c_19])).

cnf(c_200,plain,
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
    inference(renaming,[status(thm)],[c_199])).

cnf(c_897,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_200])).

cnf(c_1449,plain,
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
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ v1_xboole_0(X1_55)
    | v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1429,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
    | v1_xboole_0(X1_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_1656,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X0_55,X4_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X0_55,X4_55))
    | k2_partfun1(k4_subset_1(X3_55,X0_55,X4_55),X1_55,k1_tmap_1(X3_55,X1_55,X0_55,X4_55,X2_55,X5_55),X4_55) = X5_55
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1449,c_1429])).

cnf(c_6554,plain,
    ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
    | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3002,c_1656])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_18524,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),X0_55) = X1_55
    | k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6554,c_37,c_38,c_43,c_44,c_45])).

cnf(c_18525,plain,
    ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
    | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_18524])).

cnf(c_18546,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
    | k2_partfun1(sK3,sK1,X0_55,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2457,c_18525])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_258,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_515,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_516,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_518,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_33,c_31])).

cnf(c_582,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_258,c_518])).

cnf(c_583,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_893,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_18643,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_55,k1_xboole_0)
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18546,c_893])).

cnf(c_18644,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0_55,k1_xboole_0)
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18643,c_2457])).

cnf(c_2,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_920,plain,
    ( k4_xboole_0(k1_xboole_0,X0_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_917,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1430,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_2381,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1430])).

cnf(c_3,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_587,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k4_xboole_0(X2,X3) != X1
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_588,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k4_xboole_0(X1,k1_relat_1(X0))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_892,plain,
    ( ~ v1_relat_1(X0_55)
    | k7_relat_1(X0_55,k4_xboole_0(X1_55,k1_relat_1(X0_55))) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_588])).

cnf(c_1452,plain,
    ( k7_relat_1(X0_55,k4_xboole_0(X1_55,k1_relat_1(X0_55))) = k1_xboole_0
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_892])).

cnf(c_3111,plain,
    ( k7_relat_1(sK4,k4_xboole_0(X0_55,k1_relat_1(sK4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2381,c_1452])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_452,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_14])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_14,c_10,c_9])).

cnf(c_457,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_528,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_457])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_14,c_11,c_10,c_9])).

cnf(c_533,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_532])).

cnf(c_896,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | v1_xboole_0(X2_55)
    | k1_relat_1(X0_55) = X1_55 ),
    inference(subtyping,[status(esa)],[c_533])).

cnf(c_1450,plain,
    ( k1_relat_1(X0_55) = X1_55
    | v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_3197,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1450])).

cnf(c_1884,plain,
    ( ~ v1_funct_2(sK4,X0_55,X1_55)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_55)
    | k1_relat_1(sK4) = X0_55 ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_2112,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_1884])).

cnf(c_3412,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3197,c_34,c_28,c_27,c_26,c_2112])).

cnf(c_3627,plain,
    ( k7_relat_1(sK4,k4_xboole_0(X0_55,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3111,c_3412])).

cnf(c_3630,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_920,c_3627])).

cnf(c_18645,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
    | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18644,c_893,c_3630])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19117,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18645,c_39,c_40,c_41])).

cnf(c_19118,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
    | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_19117])).

cnf(c_19128,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2997,c_19118])).

cnf(c_2380,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_1430])).

cnf(c_3110,plain,
    ( k7_relat_1(sK5,k4_xboole_0(X0_55,k1_relat_1(sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2380,c_1452])).

cnf(c_3196,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_1450])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1879,plain,
    ( ~ v1_funct_2(sK5,X0_55,X1_55)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_55)
    | k1_relat_1(sK5) = X0_55 ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_2109,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_3217,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3196,c_34,c_25,c_24,c_23,c_2109])).

cnf(c_3556,plain,
    ( k7_relat_1(sK5,k4_xboole_0(X0_55,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3110,c_3217])).

cnf(c_3559,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_920,c_3556])).

cnf(c_19129,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19128,c_3559])).

cnf(c_19130,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19129])).

cnf(c_914,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1433,plain,
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
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_914])).

cnf(c_1601,plain,
    ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
    | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X3_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1433,c_1429])).

cnf(c_4405,plain,
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
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_1601,c_1431])).

cnf(c_912,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55))
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1435,plain,
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
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_1549,plain,
    ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
    | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X3_55) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55)) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1435,c_1429])).

cnf(c_7127,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
    | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
    | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X4_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X3_55) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4405,c_1549])).

cnf(c_7131,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
    | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_7127])).

cnf(c_46,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_47,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7230,plain,
    ( v1_funct_1(X2_55) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
    | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7131,c_37,c_40,c_46,c_47])).

cnf(c_7231,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
    | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_7230])).

cnf(c_7244,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_7231])).

cnf(c_7600,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7244,c_38,c_43,c_44])).

cnf(c_7609,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_7600])).

cnf(c_7614,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7609,c_39])).

cnf(c_19131,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19130,c_7614])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f94])).

cnf(c_192,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_21,c_20,c_19])).

cnf(c_193,plain,
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
    inference(renaming,[status(thm)],[c_192])).

cnf(c_898,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_1448,plain,
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
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_1628,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X0_55,X4_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X0_55,X4_55))
    | k2_partfun1(k4_subset_1(X3_55,X0_55,X4_55),X1_55,k1_tmap_1(X3_55,X1_55,X0_55,X4_55,X2_55,X5_55),X0_55) = X2_55
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1448,c_1429])).

cnf(c_5929,plain,
    ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
    | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),sK2) = sK4
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3002,c_1628])).

cnf(c_15491,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),sK2) = sK4
    | k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5929,c_37,c_38,c_43,c_44,c_45])).

cnf(c_15492,plain,
    ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
    | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),sK2) = sK4
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_15491])).

cnf(c_15513,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_55,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2457,c_15492])).

cnf(c_15610,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_55,k1_xboole_0)
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15513,c_893])).

cnf(c_15611,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0_55,k1_xboole_0)
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15610,c_2457])).

cnf(c_15612,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15611,c_893,c_3630])).

cnf(c_15912,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15612,c_39,c_40,c_41])).

cnf(c_15913,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_55,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_15912])).

cnf(c_15923,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2997,c_15913])).

cnf(c_15924,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15923,c_3559])).

cnf(c_15925,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15924])).

cnf(c_15926,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15925,c_7614])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_911,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2689,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2457,c_911])).

cnf(c_2690,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2689,c_893])).

cnf(c_3103,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2690,c_2997,c_3002])).

cnf(c_3904,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3559,c_3103])).

cnf(c_4102,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3904,c_3630])).

cnf(c_4103,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_4102])).

cnf(c_7618,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_7614,c_4103])).

cnf(c_7619,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_7618,c_7614])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19131,c_15926,c_7619,c_48,c_47,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:43:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.61/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.49  
% 7.61/1.49  ------  iProver source info
% 7.61/1.49  
% 7.61/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.49  git: non_committed_changes: false
% 7.61/1.49  git: last_make_outside_of_git: false
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  ------ Parsing...
% 7.61/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.49  ------ Proving...
% 7.61/1.49  ------ Problem Properties 
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  clauses                                 30
% 7.61/1.49  conjectures                             13
% 7.61/1.49  EPR                                     8
% 7.61/1.49  Horn                                    23
% 7.61/1.49  unary                                   15
% 7.61/1.49  binary                                  3
% 7.61/1.49  lits                                    125
% 7.61/1.49  lits eq                                 20
% 7.61/1.49  fd_pure                                 0
% 7.61/1.49  fd_pseudo                               0
% 7.61/1.49  fd_cond                                 0
% 7.61/1.49  fd_pseudo_cond                          1
% 7.61/1.49  AC symbols                              0
% 7.61/1.49  
% 7.61/1.49  ------ Input Options Time Limit: Unbounded
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  Current options:
% 7.61/1.49  ------ 
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  ------ Proving...
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS status Theorem for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  fof(f16,conjecture,(
% 7.61/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f17,negated_conjecture,(
% 7.61/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.61/1.49    inference(negated_conjecture,[],[f16])).
% 7.61/1.49  
% 7.61/1.49  fof(f36,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f17])).
% 7.61/1.49  
% 7.61/1.49  fof(f37,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.61/1.49    inference(flattening,[],[f36])).
% 7.61/1.49  
% 7.61/1.49  fof(f48,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f47,plain,(
% 7.61/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f46,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f45,plain,(
% 7.61/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f44,plain,(
% 7.61/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f43,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f49,plain,(
% 7.61/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.61/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f48,f47,f46,f45,f44,f43])).
% 7.61/1.49  
% 7.61/1.49  fof(f85,plain,(
% 7.61/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f13,axiom,(
% 7.61/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f30,plain,(
% 7.61/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.61/1.49    inference(ennf_transformation,[],[f13])).
% 7.61/1.49  
% 7.61/1.49  fof(f31,plain,(
% 7.61/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.61/1.49    inference(flattening,[],[f30])).
% 7.61/1.49  
% 7.61/1.49  fof(f66,plain,(
% 7.61/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f31])).
% 7.61/1.49  
% 7.61/1.49  fof(f83,plain,(
% 7.61/1.49    v1_funct_1(sK5)),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f78,plain,(
% 7.61/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f4,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f19,plain,(
% 7.61/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f4])).
% 7.61/1.49  
% 7.61/1.49  fof(f54,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f19])).
% 7.61/1.49  
% 7.61/1.49  fof(f6,axiom,(
% 7.61/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f56,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f6])).
% 7.61/1.49  
% 7.61/1.49  fof(f89,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.61/1.49    inference(definition_unfolding,[],[f54,f56])).
% 7.61/1.49  
% 7.61/1.49  fof(f82,plain,(
% 7.61/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f80,plain,(
% 7.61/1.49    v1_funct_1(sK4)),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f14,axiom,(
% 7.61/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f32,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f14])).
% 7.61/1.49  
% 7.61/1.49  fof(f33,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.61/1.49    inference(flattening,[],[f32])).
% 7.61/1.49  
% 7.61/1.49  fof(f41,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.61/1.49    inference(nnf_transformation,[],[f33])).
% 7.61/1.49  
% 7.61/1.49  fof(f42,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.61/1.49    inference(flattening,[],[f41])).
% 7.61/1.49  
% 7.61/1.49  fof(f68,plain,(
% 7.61/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f42])).
% 7.61/1.49  
% 7.61/1.49  fof(f93,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.49    inference(equality_resolution,[],[f68])).
% 7.61/1.49  
% 7.61/1.49  fof(f15,axiom,(
% 7.61/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f34,plain,(
% 7.61/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f15])).
% 7.61/1.49  
% 7.61/1.49  fof(f35,plain,(
% 7.61/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.61/1.49    inference(flattening,[],[f34])).
% 7.61/1.49  
% 7.61/1.49  fof(f70,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f35])).
% 7.61/1.49  
% 7.61/1.49  fof(f71,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f35])).
% 7.61/1.49  
% 7.61/1.49  fof(f72,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f35])).
% 7.61/1.49  
% 7.61/1.49  fof(f5,axiom,(
% 7.61/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f20,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f5])).
% 7.61/1.49  
% 7.61/1.49  fof(f55,plain,(
% 7.61/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f20])).
% 7.61/1.49  
% 7.61/1.49  fof(f74,plain,(
% 7.61/1.49    ~v1_xboole_0(sK1)),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f75,plain,(
% 7.61/1.49    ~v1_xboole_0(sK2)),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f81,plain,(
% 7.61/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f1,axiom,(
% 7.61/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f38,plain,(
% 7.61/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.61/1.49    inference(nnf_transformation,[],[f1])).
% 7.61/1.49  
% 7.61/1.49  fof(f50,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f38])).
% 7.61/1.49  
% 7.61/1.49  fof(f88,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f50,f56])).
% 7.61/1.49  
% 7.61/1.49  fof(f8,axiom,(
% 7.61/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f22,plain,(
% 7.61/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f8])).
% 7.61/1.49  
% 7.61/1.49  fof(f23,plain,(
% 7.61/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.61/1.49    inference(flattening,[],[f22])).
% 7.61/1.49  
% 7.61/1.49  fof(f39,plain,(
% 7.61/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.61/1.49    inference(nnf_transformation,[],[f23])).
% 7.61/1.49  
% 7.61/1.49  fof(f58,plain,(
% 7.61/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f39])).
% 7.61/1.49  
% 7.61/1.49  fof(f79,plain,(
% 7.61/1.49    r1_subset_1(sK2,sK3)),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f77,plain,(
% 7.61/1.49    ~v1_xboole_0(sK3)),
% 7.61/1.49    inference(cnf_transformation,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f2,axiom,(
% 7.61/1.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f52,plain,(
% 7.61/1.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f2])).
% 7.61/1.49  
% 7.61/1.49  fof(f9,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f24,plain,(
% 7.61/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.61/1.50    inference(ennf_transformation,[],[f9])).
% 7.61/1.50  
% 7.61/1.50  fof(f60,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.61/1.50    inference(cnf_transformation,[],[f24])).
% 7.61/1.50  
% 7.61/1.50  fof(f3,axiom,(
% 7.61/1.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f53,plain,(
% 7.61/1.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f3])).
% 7.61/1.50  
% 7.61/1.50  fof(f7,axiom,(
% 7.61/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f21,plain,(
% 7.61/1.50    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.61/1.50    inference(ennf_transformation,[],[f7])).
% 7.61/1.50  
% 7.61/1.50  fof(f57,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f21])).
% 7.61/1.50  
% 7.61/1.50  fof(f11,axiom,(
% 7.61/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f26,plain,(
% 7.61/1.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.61/1.50    inference(ennf_transformation,[],[f11])).
% 7.61/1.50  
% 7.61/1.50  fof(f27,plain,(
% 7.61/1.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.61/1.50    inference(flattening,[],[f26])).
% 7.61/1.50  
% 7.61/1.50  fof(f63,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f27])).
% 7.61/1.50  
% 7.61/1.50  fof(f10,axiom,(
% 7.61/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f18,plain,(
% 7.61/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.61/1.50    inference(pure_predicate_removal,[],[f10])).
% 7.61/1.50  
% 7.61/1.50  fof(f25,plain,(
% 7.61/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.61/1.50    inference(ennf_transformation,[],[f18])).
% 7.61/1.50  
% 7.61/1.50  fof(f61,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.61/1.50    inference(cnf_transformation,[],[f25])).
% 7.61/1.50  
% 7.61/1.50  fof(f12,axiom,(
% 7.61/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f28,plain,(
% 7.61/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.61/1.50    inference(ennf_transformation,[],[f12])).
% 7.61/1.50  
% 7.61/1.50  fof(f29,plain,(
% 7.61/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.61/1.50    inference(flattening,[],[f28])).
% 7.61/1.50  
% 7.61/1.50  fof(f40,plain,(
% 7.61/1.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.61/1.50    inference(nnf_transformation,[],[f29])).
% 7.61/1.50  
% 7.61/1.50  fof(f64,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f40])).
% 7.61/1.50  
% 7.61/1.50  fof(f76,plain,(
% 7.61/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.61/1.50    inference(cnf_transformation,[],[f49])).
% 7.61/1.50  
% 7.61/1.50  fof(f84,plain,(
% 7.61/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.61/1.50    inference(cnf_transformation,[],[f49])).
% 7.61/1.50  
% 7.61/1.50  fof(f67,plain,(
% 7.61/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f42])).
% 7.61/1.50  
% 7.61/1.50  fof(f94,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.50    inference(equality_resolution,[],[f67])).
% 7.61/1.50  
% 7.61/1.50  fof(f86,plain,(
% 7.61/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.61/1.50    inference(cnf_transformation,[],[f49])).
% 7.61/1.50  
% 7.61/1.50  cnf(c_23,negated_conjecture,
% 7.61/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.61/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_910,negated_conjecture,
% 7.61/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_23]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1436,plain,
% 7.61/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.61/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_916,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.61/1.50      | ~ v1_funct_1(X0_55)
% 7.61/1.50      | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_15]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1431,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X2_55) != iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2563,plain,
% 7.61/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55)
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1436,c_1431]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_25,negated_conjecture,
% 7.61/1.50      ( v1_funct_1(sK5) ),
% 7.61/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1889,plain,
% 7.61/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.61/1.50      | ~ v1_funct_1(sK5)
% 7.61/1.50      | k2_partfun1(X0_55,X1_55,sK5,X2_55) = k7_relat_1(sK5,X2_55) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_916]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2115,plain,
% 7.61/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.61/1.50      | ~ v1_funct_1(sK5)
% 7.61/1.50      | k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_1889]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2997,plain,
% 7.61/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_2563,c_25,c_23,c_2115]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_30,negated_conjecture,
% 7.61/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.61/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_904,negated_conjecture,
% 7.61/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_30]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1442,plain,
% 7.61/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_904]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_4,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.61/1.50      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.61/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_919,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 7.61/1.50      | k9_subset_1(X1_55,X2_55,X0_55) = k1_setfam_1(k2_tarski(X2_55,X0_55)) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1428,plain,
% 7.61/1.50      ( k9_subset_1(X0_55,X1_55,X2_55) = k1_setfam_1(k2_tarski(X1_55,X2_55))
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2457,plain,
% 7.61/1.50      ( k9_subset_1(sK0,X0_55,sK3) = k1_setfam_1(k2_tarski(X0_55,sK3)) ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1442,c_1428]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_26,negated_conjecture,
% 7.61/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.61/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_907,negated_conjecture,
% 7.61/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_26]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1439,plain,
% 7.61/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2564,plain,
% 7.61/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55)
% 7.61/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1439,c_1431]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_28,negated_conjecture,
% 7.61/1.50      ( v1_funct_1(sK4) ),
% 7.61/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1894,plain,
% 7.61/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.61/1.50      | ~ v1_funct_1(sK4)
% 7.61/1.50      | k2_partfun1(X0_55,X1_55,sK4,X2_55) = k7_relat_1(sK4,X2_55) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_916]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2120,plain,
% 7.61/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.61/1.50      | ~ v1_funct_1(sK4)
% 7.61/1.50      | k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_1894]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3002,plain,
% 7.61/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_2564,c_28,c_26,c_2120]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_17,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_1(X3)
% 7.61/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X1)
% 7.61/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.61/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_21,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_1(X3)
% 7.61/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X1) ),
% 7.61/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_20,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_1(X3)
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X1) ),
% 7.61/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_19,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_1(X3)
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X1) ),
% 7.61/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_199,plain,
% 7.61/1.50      ( ~ v1_funct_1(X3)
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X1)
% 7.61/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_17,c_21,c_20,c_19]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_200,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_1(X3)
% 7.61/1.50      | v1_xboole_0(X1)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_199]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_897,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 7.61/1.50      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 7.61/1.50      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 7.61/1.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 7.61/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.61/1.50      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 7.61/1.50      | ~ v1_funct_1(X0_55)
% 7.61/1.50      | ~ v1_funct_1(X3_55)
% 7.61/1.50      | v1_xboole_0(X2_55)
% 7.61/1.50      | v1_xboole_0(X1_55)
% 7.61/1.50      | v1_xboole_0(X4_55)
% 7.61/1.50      | v1_xboole_0(X5_55)
% 7.61/1.50      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_200]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1449,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
% 7.61/1.50      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X2_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X5_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X3_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X4_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_897]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_5,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.61/1.50      | ~ v1_xboole_0(X1)
% 7.61/1.50      | v1_xboole_0(X0) ),
% 7.61/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_918,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 7.61/1.50      | ~ v1_xboole_0(X1_55)
% 7.61/1.50      | v1_xboole_0(X0_55) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1429,plain,
% 7.61/1.50      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1656,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X0_55,X4_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X0_55,X4_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X3_55,X0_55,X4_55),X1_55,k1_tmap_1(X3_55,X1_55,X0_55,X4_55,X2_55,X5_55),X4_55) = X5_55
% 7.61/1.50      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X5_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X2_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X4_55) = iProver_top ),
% 7.61/1.50      inference(forward_subsumption_resolution,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_1449,c_1429]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_6554,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),X0_55) = X1_55
% 7.61/1.50      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 7.61/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | v1_funct_1(X1_55) != iProver_top
% 7.61/1.50      | v1_funct_1(sK4) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.61/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_3002,c_1656]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_34,negated_conjecture,
% 7.61/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.61/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_37,plain,
% 7.61/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_33,negated_conjecture,
% 7.61/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.61/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_38,plain,
% 7.61/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_43,plain,
% 7.61/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_27,negated_conjecture,
% 7.61/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.61/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_44,plain,
% 7.61/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_45,plain,
% 7.61/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_18524,plain,
% 7.61/1.50      ( v1_funct_1(X1_55) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 7.61/1.50      | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),X0_55) = X1_55
% 7.61/1.50      | k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_6554,c_37,c_38,c_43,c_44,c_45]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_18525,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),X0_55) = X1_55
% 7.61/1.50      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | v1_funct_1(X1_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_18524]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_18546,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
% 7.61/1.50      | k2_partfun1(sK3,sK1,X0_55,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_2457,c_18525]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1,plain,
% 7.61/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.61/1.50      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.61/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_258,plain,
% 7.61/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.61/1.50      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.61/1.50      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_8,plain,
% 7.61/1.50      ( ~ r1_subset_1(X0,X1)
% 7.61/1.50      | r1_xboole_0(X0,X1)
% 7.61/1.50      | v1_xboole_0(X0)
% 7.61/1.50      | v1_xboole_0(X1) ),
% 7.61/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_29,negated_conjecture,
% 7.61/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.61/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_515,plain,
% 7.61/1.50      ( r1_xboole_0(X0,X1)
% 7.61/1.50      | v1_xboole_0(X0)
% 7.61/1.50      | v1_xboole_0(X1)
% 7.61/1.50      | sK3 != X1
% 7.61/1.50      | sK2 != X0 ),
% 7.61/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_516,plain,
% 7.61/1.50      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.61/1.50      inference(unflattening,[status(thm)],[c_515]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_31,negated_conjecture,
% 7.61/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.61/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_518,plain,
% 7.61/1.50      ( r1_xboole_0(sK2,sK3) ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_516,c_33,c_31]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_582,plain,
% 7.61/1.50      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 7.61/1.50      | sK3 != X1
% 7.61/1.50      | sK2 != X0 ),
% 7.61/1.50      inference(resolution_lifted,[status(thm)],[c_258,c_518]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_583,plain,
% 7.61/1.50      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.61/1.50      inference(unflattening,[status(thm)],[c_582]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_893,plain,
% 7.61/1.50      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_583]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_18643,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
% 7.61/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_55,k1_xboole_0)
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_18546,c_893]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_18644,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
% 7.61/1.50      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0_55,k1_xboole_0)
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_18643,c_2457]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2,plain,
% 7.61/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.61/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_920,plain,
% 7.61/1.50      ( k4_xboole_0(k1_xboole_0,X0_55) = k1_xboole_0 ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_9,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | v1_relat_1(X0) ),
% 7.61/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_917,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.61/1.50      | v1_relat_1(X0_55) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1430,plain,
% 7.61/1.50      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 7.61/1.50      | v1_relat_1(X0_55) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_917]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2381,plain,
% 7.61/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1439,c_1430]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3,plain,
% 7.61/1.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.61/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_6,plain,
% 7.61/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.61/1.50      | ~ v1_relat_1(X1)
% 7.61/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.61/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_587,plain,
% 7.61/1.50      ( ~ v1_relat_1(X0)
% 7.61/1.50      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.61/1.50      | k4_xboole_0(X2,X3) != X1
% 7.61/1.50      | k1_relat_1(X0) != X3 ),
% 7.61/1.50      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_588,plain,
% 7.61/1.50      ( ~ v1_relat_1(X0)
% 7.61/1.50      | k7_relat_1(X0,k4_xboole_0(X1,k1_relat_1(X0))) = k1_xboole_0 ),
% 7.61/1.50      inference(unflattening,[status(thm)],[c_587]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_892,plain,
% 7.61/1.50      ( ~ v1_relat_1(X0_55)
% 7.61/1.50      | k7_relat_1(X0_55,k4_xboole_0(X1_55,k1_relat_1(X0_55))) = k1_xboole_0 ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_588]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1452,plain,
% 7.61/1.50      ( k7_relat_1(X0_55,k4_xboole_0(X1_55,k1_relat_1(X0_55))) = k1_xboole_0
% 7.61/1.50      | v1_relat_1(X0_55) != iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_892]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3111,plain,
% 7.61/1.50      ( k7_relat_1(sK4,k4_xboole_0(X0_55,k1_relat_1(sK4))) = k1_xboole_0 ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_2381,c_1452]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_11,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | v1_partfun1(X0,X1)
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | v1_xboole_0(X2) ),
% 7.61/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_10,plain,
% 7.61/1.50      ( v4_relat_1(X0,X1)
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.61/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_14,plain,
% 7.61/1.50      ( ~ v1_partfun1(X0,X1)
% 7.61/1.50      | ~ v4_relat_1(X0,X1)
% 7.61/1.50      | ~ v1_relat_1(X0)
% 7.61/1.50      | k1_relat_1(X0) = X1 ),
% 7.61/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_452,plain,
% 7.61/1.50      ( ~ v1_partfun1(X0,X1)
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ v1_relat_1(X0)
% 7.61/1.50      | k1_relat_1(X0) = X1 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_10,c_14]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_456,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ v1_partfun1(X0,X1)
% 7.61/1.50      | k1_relat_1(X0) = X1 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_452,c_14,c_10,c_9]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_457,plain,
% 7.61/1.50      ( ~ v1_partfun1(X0,X1)
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | k1_relat_1(X0) = X1 ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_456]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_528,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | k1_relat_1(X0) = X1 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_11,c_457]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_532,plain,
% 7.61/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | k1_relat_1(X0) = X1 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_528,c_14,c_11,c_10,c_9]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_533,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | k1_relat_1(X0) = X1 ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_532]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_896,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 7.61/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.61/1.50      | ~ v1_funct_1(X0_55)
% 7.61/1.50      | v1_xboole_0(X2_55)
% 7.61/1.50      | k1_relat_1(X0_55) = X1_55 ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_533]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1450,plain,
% 7.61/1.50      ( k1_relat_1(X0_55) = X1_55
% 7.61/1.50      | v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X2_55) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_896]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3197,plain,
% 7.61/1.50      ( k1_relat_1(sK4) = sK2
% 7.61/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.61/1.50      | v1_funct_1(sK4) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1439,c_1450]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1884,plain,
% 7.61/1.50      ( ~ v1_funct_2(sK4,X0_55,X1_55)
% 7.61/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.61/1.50      | ~ v1_funct_1(sK4)
% 7.61/1.50      | v1_xboole_0(X1_55)
% 7.61/1.50      | k1_relat_1(sK4) = X0_55 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_896]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2112,plain,
% 7.61/1.50      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.61/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.61/1.50      | ~ v1_funct_1(sK4)
% 7.61/1.50      | v1_xboole_0(sK1)
% 7.61/1.50      | k1_relat_1(sK4) = sK2 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_1884]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3412,plain,
% 7.61/1.50      ( k1_relat_1(sK4) = sK2 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_3197,c_34,c_28,c_27,c_26,c_2112]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3627,plain,
% 7.61/1.50      ( k7_relat_1(sK4,k4_xboole_0(X0_55,sK2)) = k1_xboole_0 ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_3111,c_3412]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3630,plain,
% 7.61/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_920,c_3627]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_18645,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
% 7.61/1.50      | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_18644,c_893,c_3630]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_32,negated_conjecture,
% 7.61/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.61/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_39,plain,
% 7.61/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_40,plain,
% 7.61/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_41,plain,
% 7.61/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_19117,plain,
% 7.61/1.50      ( v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_18645,c_39,c_40,c_41]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_19118,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK3) = X0_55
% 7.61/1.50      | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_19117]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_19128,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.61/1.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_2997,c_19118]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2380,plain,
% 7.61/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1436,c_1430]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3110,plain,
% 7.61/1.50      ( k7_relat_1(sK5,k4_xboole_0(X0_55,k1_relat_1(sK5))) = k1_xboole_0 ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_2380,c_1452]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3196,plain,
% 7.61/1.50      ( k1_relat_1(sK5) = sK3
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1436,c_1450]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_24,negated_conjecture,
% 7.61/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.61/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1879,plain,
% 7.61/1.50      ( ~ v1_funct_2(sK5,X0_55,X1_55)
% 7.61/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.61/1.50      | ~ v1_funct_1(sK5)
% 7.61/1.50      | v1_xboole_0(X1_55)
% 7.61/1.50      | k1_relat_1(sK5) = X0_55 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_896]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2109,plain,
% 7.61/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.61/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.61/1.50      | ~ v1_funct_1(sK5)
% 7.61/1.50      | v1_xboole_0(sK1)
% 7.61/1.50      | k1_relat_1(sK5) = sK3 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_1879]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3217,plain,
% 7.61/1.50      ( k1_relat_1(sK5) = sK3 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_3196,c_34,c_25,c_24,c_23,c_2109]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3556,plain,
% 7.61/1.50      ( k7_relat_1(sK5,k4_xboole_0(X0_55,sK3)) = k1_xboole_0 ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_3110,c_3217]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3559,plain,
% 7.61/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_920,c_3556]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_19129,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.61/1.50      | k1_xboole_0 != k1_xboole_0
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_19128,c_3559]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_19130,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(equality_resolution_simp,[status(thm)],[c_19129]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_914,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 7.61/1.50      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 7.61/1.50      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 7.61/1.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 7.61/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.61/1.50      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 7.61/1.50      | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55)))
% 7.61/1.50      | ~ v1_funct_1(X0_55)
% 7.61/1.50      | ~ v1_funct_1(X3_55)
% 7.61/1.50      | v1_xboole_0(X2_55)
% 7.61/1.50      | v1_xboole_0(X1_55)
% 7.61/1.50      | v1_xboole_0(X4_55)
% 7.61/1.50      | v1_xboole_0(X5_55) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_19]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1433,plain,
% 7.61/1.50      ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55))) = iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X3_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X5_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X2_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X4_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_914]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1601,plain,
% 7.61/1.50      ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55))) = iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X3_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X2_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X4_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top ),
% 7.61/1.50      inference(forward_subsumption_resolution,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_1433,c_1429]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_4405,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
% 7.61/1.50      | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X5_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X4_55) != iProver_top
% 7.61/1.50      | v1_funct_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55)) != iProver_top
% 7.61/1.50      | v1_xboole_0(X3_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X2_55) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1601,c_1431]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_912,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 7.61/1.50      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 7.61/1.50      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 7.61/1.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 7.61/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.61/1.50      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 7.61/1.50      | ~ v1_funct_1(X0_55)
% 7.61/1.50      | ~ v1_funct_1(X3_55)
% 7.61/1.50      | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55))
% 7.61/1.50      | v1_xboole_0(X2_55)
% 7.61/1.50      | v1_xboole_0(X1_55)
% 7.61/1.50      | v1_xboole_0(X4_55)
% 7.61/1.50      | v1_xboole_0(X5_55) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_21]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1435,plain,
% 7.61/1.50      ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X3_55) != iProver_top
% 7.61/1.50      | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55)) = iProver_top
% 7.61/1.50      | v1_xboole_0(X5_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X2_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X4_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1549,plain,
% 7.61/1.50      ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X3_55) != iProver_top
% 7.61/1.50      | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55)) = iProver_top
% 7.61/1.50      | v1_xboole_0(X2_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X4_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top ),
% 7.61/1.50      inference(forward_subsumption_resolution,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_1435,c_1429]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7127,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
% 7.61/1.50      | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X5_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X4_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X2_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X3_55) = iProver_top ),
% 7.61/1.50      inference(forward_subsumption_resolution,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_4405,c_1549]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7131,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
% 7.61/1.50      | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | v1_funct_1(X2_55) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1436,c_7127]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_46,plain,
% 7.61/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_47,plain,
% 7.61/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7230,plain,
% 7.61/1.50      ( v1_funct_1(X2_55) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
% 7.61/1.50      | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_7131,c_37,c_40,c_46,c_47]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7231,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
% 7.61/1.50      | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | v1_funct_1(X2_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_7230]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7244,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
% 7.61/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | v1_funct_1(sK4) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1439,c_7231]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7600,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_7244,c_38,c_43,c_44]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7609,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55)
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_1442,c_7600]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7614,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_7609,c_39]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_19131,plain,
% 7.61/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_19130,c_7614]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_18,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_1(X3)
% 7.61/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X1)
% 7.61/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.61/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_192,plain,
% 7.61/1.50      ( ~ v1_funct_1(X3)
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X1)
% 7.61/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_18,c_21,c_20,c_19]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_193,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.50      | ~ v1_funct_1(X0)
% 7.61/1.50      | ~ v1_funct_1(X3)
% 7.61/1.50      | v1_xboole_0(X1)
% 7.61/1.50      | v1_xboole_0(X2)
% 7.61/1.50      | v1_xboole_0(X4)
% 7.61/1.50      | v1_xboole_0(X5)
% 7.61/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_192]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_898,plain,
% 7.61/1.50      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 7.61/1.50      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 7.61/1.50      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 7.61/1.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 7.61/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.61/1.50      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 7.61/1.50      | ~ v1_funct_1(X0_55)
% 7.61/1.50      | ~ v1_funct_1(X3_55)
% 7.61/1.50      | v1_xboole_0(X2_55)
% 7.61/1.50      | v1_xboole_0(X1_55)
% 7.61/1.50      | v1_xboole_0(X4_55)
% 7.61/1.50      | v1_xboole_0(X5_55)
% 7.61/1.50      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_193]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1448,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
% 7.61/1.50      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X2_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X5_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X3_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X4_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1628,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X0_55,X4_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X0_55,X4_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X3_55,X0_55,X4_55),X1_55,k1_tmap_1(X3_55,X1_55,X0_55,X4_55,X2_55,X5_55),X0_55) = X2_55
% 7.61/1.50      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 7.61/1.50      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 7.61/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.61/1.50      | v1_funct_1(X5_55) != iProver_top
% 7.61/1.50      | v1_funct_1(X2_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X1_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(X4_55) = iProver_top ),
% 7.61/1.50      inference(forward_subsumption_resolution,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_1448,c_1429]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_5929,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),sK2) = sK4
% 7.61/1.50      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 7.61/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | v1_funct_1(X1_55) != iProver_top
% 7.61/1.50      | v1_funct_1(sK4) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top
% 7.61/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.61/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_3002,c_1628]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15491,plain,
% 7.61/1.50      ( v1_funct_1(X1_55) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 7.61/1.50      | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),sK2) = sK4
% 7.61/1.50      | k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_5929,c_37,c_38,c_43,c_44,c_45]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15492,plain,
% 7.61/1.50      ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,sK2,X0_55)) != k7_relat_1(sK4,k9_subset_1(X2_55,sK2,X0_55))
% 7.61/1.50      | k2_partfun1(k4_subset_1(X2_55,sK2,X0_55),sK1,k1_tmap_1(X2_55,sK1,sK2,X0_55,sK4,X1_55),sK2) = sK4
% 7.61/1.50      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_55)) != iProver_top
% 7.61/1.50      | v1_funct_1(X1_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_15491]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15513,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
% 7.61/1.50      | k2_partfun1(sK3,sK1,X0_55,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_2457,c_15492]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15610,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
% 7.61/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_55,k1_xboole_0)
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_15513,c_893]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15611,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
% 7.61/1.50      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0_55,k1_xboole_0)
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_15610,c_2457]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15612,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
% 7.61/1.50      | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_15611,c_893,c_3630]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15912,plain,
% 7.61/1.50      ( v1_funct_1(X0_55) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_15612,c_39,c_40,c_41]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15913,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_55),sK2) = sK4
% 7.61/1.50      | k2_partfun1(sK3,sK1,X0_55,k1_xboole_0) != k1_xboole_0
% 7.61/1.50      | v1_funct_2(X0_55,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(X0_55) != iProver_top ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_15912]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15923,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.61/1.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_2997,c_15913]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15924,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.61/1.50      | k1_xboole_0 != k1_xboole_0
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_15923,c_3559]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15925,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(equality_resolution_simp,[status(thm)],[c_15924]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_15926,plain,
% 7.61/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.61/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_15925,c_7614]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_22,negated_conjecture,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.61/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_911,negated_conjecture,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.61/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2689,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.50      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_2457,c_911]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2690,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.61/1.50      inference(light_normalisation,[status(thm)],[c_2689,c_893]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3103,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.50      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_2690,c_2997,c_3002]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3904,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.50      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_3559,c_3103]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_4102,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_3904,c_3630]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_4103,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.61/1.50      inference(renaming,[status(thm)],[c_4102]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7618,plain,
% 7.61/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_7614,c_4103]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7619,plain,
% 7.61/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.61/1.50      inference(demodulation,[status(thm)],[c_7618,c_7614]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_48,plain,
% 7.61/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(contradiction,plain,
% 7.61/1.50      ( $false ),
% 7.61/1.50      inference(minisat,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_19131,c_15926,c_7619,c_48,c_47,c_46]) ).
% 7.61/1.50  
% 7.61/1.50  
% 7.61/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.50  
% 7.61/1.50  ------                               Statistics
% 7.61/1.50  
% 7.61/1.50  ------ Selected
% 7.61/1.50  
% 7.61/1.50  total_time:                             0.789
% 7.61/1.50  
%------------------------------------------------------------------------------
