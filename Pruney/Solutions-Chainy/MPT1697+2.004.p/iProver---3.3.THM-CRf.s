%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:22 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  211 (2201 expanded)
%              Number of clauses        :  143 ( 608 expanded)
%              Number of leaves         :   18 ( 843 expanded)
%              Depth                    :   26
%              Number of atoms          : 1258 (27968 expanded)
%              Number of equality atoms :  568 (6882 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f47,f46,f45,f44,f43,f42])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f40,plain,(
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
    inference(flattening,[],[f40])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
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
    inference(equality_resolution,[],[f66])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f68,plain,(
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

fof(f69,plain,(
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

fof(f70,plain,(
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

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f84,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_843,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1345,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_849,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1340,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_2523,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_1340])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1791,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_2012,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(c_2954,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2523,c_25,c_23,c_2012])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_837,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1351,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_852,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1337,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_2383,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1351,c_1337])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_840,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1348,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_2524,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1340])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1796,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_2017,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_2959,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_28,c_26,c_2017])).

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
    inference(cnf_transformation,[],[f88])).

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
    inference(cnf_transformation,[],[f68])).

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
    inference(cnf_transformation,[],[f69])).

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
    inference(cnf_transformation,[],[f70])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_21,c_20,c_19])).

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

cnf(c_830,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
    | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_196])).

cnf(c_1358,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
    | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_851,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1338,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_xboole_0(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_1560,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
    | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1358,c_1338])).

cnf(c_6932,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2959,c_1560])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25021,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6932,c_37,c_38,c_43,c_44,c_45])).

cnf(c_25022,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_25021])).

cnf(c_25043,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2383,c_25022])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_252,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_505,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_506,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_508,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_33,c_31])).

cnf(c_534,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_508])).

cnf(c_535,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_828,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_535])).

cnf(c_25140,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_53,k1_xboole_0)
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25043,c_828])).

cnf(c_25141,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_25140,c_2383])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1339,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_2290,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1339])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_853,plain,
    ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_854,plain,
    ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1978,plain,
    ( k3_xboole_0(k1_xboole_0,X0_53) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_853,c_854])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_250,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_519,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(X2,X3) != k1_xboole_0
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_250,c_6])).

cnf(c_520,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_829,plain,
    ( ~ v1_relat_1(X0_53)
    | k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | k3_xboole_0(X1_53,k1_relat_1(X0_53)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_520])).

cnf(c_1359,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | k3_xboole_0(X1_53,k1_relat_1(X0_53)) != k1_xboole_0
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_3059,plain,
    ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1978,c_1359])).

cnf(c_3283,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2290,c_3059])).

cnf(c_25142,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25141,c_828,c_3283])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25379,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25142,c_39,c_40,c_41])).

cnf(c_25380,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_25379])).

cnf(c_25390,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2954,c_25380])).

cnf(c_2289,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_1339])).

cnf(c_3282,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2289,c_3059])).

cnf(c_25391,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25390,c_3282])).

cnf(c_25392,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_25391])).

cnf(c_847,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1342,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_xboole_0(X5_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_1505,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1342,c_1338])).

cnf(c_4579,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
    | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
    | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_1340])).

cnf(c_845,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1344,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
    | v1_xboole_0(X5_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_1453,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1344,c_1338])).

cnf(c_10144,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
    | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
    | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4579,c_1453])).

cnf(c_10148,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_10144])).

cnf(c_46,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_47,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10247,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10148,c_37,c_40,c_46,c_47])).

cnf(c_10248,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_10247])).

cnf(c_10261,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_10248])).

cnf(c_10739,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10261,c_38,c_43,c_44])).

cnf(c_10748,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_10739])).

cnf(c_10753,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10748,c_39])).

cnf(c_25393,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25392,c_10753])).

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
    inference(cnf_transformation,[],[f89])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_21,c_20,c_19])).

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

cnf(c_831,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
    | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_189])).

cnf(c_1357,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
    | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_1532,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
    | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1357,c_1338])).

cnf(c_5760,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2959,c_1532])).

cnf(c_14259,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5760,c_37,c_38,c_43,c_44,c_45])).

cnf(c_14260,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_14259])).

cnf(c_14281,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2383,c_14260])).

cnf(c_14378,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_53,k1_xboole_0)
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14281,c_828])).

cnf(c_14379,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14378,c_2383])).

cnf(c_14380,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14379,c_828,c_3283])).

cnf(c_15393,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14380,c_39,c_40,c_41])).

cnf(c_15394,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_15393])).

cnf(c_15404,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2954,c_15394])).

cnf(c_15405,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15404,c_3282])).

cnf(c_15406,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15405])).

cnf(c_15407,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15406,c_10753])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_844,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2642,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2383,c_844])).

cnf(c_2643,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2642,c_828])).

cnf(c_3049,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2643,c_2954,c_2959])).

cnf(c_3780,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3282,c_3049])).

cnf(c_4724,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3780,c_3283])).

cnf(c_4725,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_4724])).

cnf(c_10757,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_10753,c_4725])).

cnf(c_10758,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_10757,c_10753])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25393,c_15407,c_10758,c_48,c_47,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:21:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.68/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/1.50  
% 7.68/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.68/1.50  
% 7.68/1.50  ------  iProver source info
% 7.68/1.50  
% 7.68/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.68/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.68/1.50  git: non_committed_changes: false
% 7.68/1.50  git: last_make_outside_of_git: false
% 7.68/1.50  
% 7.68/1.50  ------ 
% 7.68/1.50  ------ Parsing...
% 7.68/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.50  ------ Proving...
% 7.68/1.50  ------ Problem Properties 
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  clauses                                 29
% 7.68/1.50  conjectures                             13
% 7.68/1.50  EPR                                     8
% 7.68/1.50  Horn                                    22
% 7.68/1.50  unary                                   15
% 7.68/1.50  binary                                  2
% 7.68/1.50  lits                                    123
% 7.68/1.50  lits eq                                 19
% 7.68/1.50  fd_pure                                 0
% 7.68/1.50  fd_pseudo                               0
% 7.68/1.50  fd_cond                                 0
% 7.68/1.50  fd_pseudo_cond                          1
% 7.68/1.50  AC symbols                              0
% 7.68/1.50  
% 7.68/1.50  ------ Input Options Time Limit: Unbounded
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  ------ 
% 7.68/1.50  Current options:
% 7.68/1.50  ------ 
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  ------ Proving...
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  % SZS status Theorem for theBenchmark.p
% 7.68/1.50  
% 7.68/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.68/1.50  
% 7.68/1.50  fof(f15,conjecture,(
% 7.68/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f16,negated_conjecture,(
% 7.68/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.68/1.50    inference(negated_conjecture,[],[f15])).
% 7.68/1.50  
% 7.68/1.50  fof(f35,plain,(
% 7.68/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.68/1.50    inference(ennf_transformation,[],[f16])).
% 7.68/1.50  
% 7.68/1.50  fof(f36,plain,(
% 7.68/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.68/1.50    inference(flattening,[],[f35])).
% 7.68/1.50  
% 7.68/1.50  fof(f47,plain,(
% 7.68/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.68/1.50    introduced(choice_axiom,[])).
% 7.68/1.50  
% 7.68/1.50  fof(f46,plain,(
% 7.68/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.68/1.50    introduced(choice_axiom,[])).
% 7.68/1.50  
% 7.68/1.50  fof(f45,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.68/1.50    introduced(choice_axiom,[])).
% 7.68/1.50  
% 7.68/1.50  fof(f44,plain,(
% 7.68/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.68/1.50    introduced(choice_axiom,[])).
% 7.68/1.50  
% 7.68/1.50  fof(f43,plain,(
% 7.68/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.68/1.50    introduced(choice_axiom,[])).
% 7.68/1.50  
% 7.68/1.50  fof(f42,plain,(
% 7.68/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.68/1.50    introduced(choice_axiom,[])).
% 7.68/1.50  
% 7.68/1.50  fof(f48,plain,(
% 7.68/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.68/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f47,f46,f45,f44,f43,f42])).
% 7.68/1.50  
% 7.68/1.50  fof(f83,plain,(
% 7.68/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f12,axiom,(
% 7.68/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f29,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.68/1.50    inference(ennf_transformation,[],[f12])).
% 7.68/1.50  
% 7.68/1.50  fof(f30,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.68/1.50    inference(flattening,[],[f29])).
% 7.68/1.50  
% 7.68/1.50  fof(f64,plain,(
% 7.68/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f30])).
% 7.68/1.50  
% 7.68/1.50  fof(f81,plain,(
% 7.68/1.50    v1_funct_1(sK5)),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f76,plain,(
% 7.68/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f4,axiom,(
% 7.68/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f18,plain,(
% 7.68/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.68/1.50    inference(ennf_transformation,[],[f4])).
% 7.68/1.50  
% 7.68/1.50  fof(f53,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f18])).
% 7.68/1.50  
% 7.68/1.50  fof(f80,plain,(
% 7.68/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f78,plain,(
% 7.68/1.50    v1_funct_1(sK4)),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f13,axiom,(
% 7.68/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f31,plain,(
% 7.68/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.68/1.50    inference(ennf_transformation,[],[f13])).
% 7.68/1.50  
% 7.68/1.50  fof(f32,plain,(
% 7.68/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.68/1.50    inference(flattening,[],[f31])).
% 7.68/1.50  
% 7.68/1.50  fof(f40,plain,(
% 7.68/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.68/1.50    inference(nnf_transformation,[],[f32])).
% 7.68/1.50  
% 7.68/1.50  fof(f41,plain,(
% 7.68/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.68/1.50    inference(flattening,[],[f40])).
% 7.68/1.50  
% 7.68/1.50  fof(f66,plain,(
% 7.68/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f41])).
% 7.68/1.50  
% 7.68/1.50  fof(f88,plain,(
% 7.68/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.68/1.50    inference(equality_resolution,[],[f66])).
% 7.68/1.50  
% 7.68/1.50  fof(f14,axiom,(
% 7.68/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f33,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.68/1.50    inference(ennf_transformation,[],[f14])).
% 7.68/1.50  
% 7.68/1.50  fof(f34,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.68/1.50    inference(flattening,[],[f33])).
% 7.68/1.50  
% 7.68/1.50  fof(f68,plain,(
% 7.68/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f34])).
% 7.68/1.50  
% 7.68/1.50  fof(f69,plain,(
% 7.68/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f34])).
% 7.68/1.50  
% 7.68/1.50  fof(f70,plain,(
% 7.68/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f34])).
% 7.68/1.50  
% 7.68/1.50  fof(f5,axiom,(
% 7.68/1.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f19,plain,(
% 7.68/1.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.68/1.50    inference(ennf_transformation,[],[f5])).
% 7.68/1.50  
% 7.68/1.50  fof(f54,plain,(
% 7.68/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f19])).
% 7.68/1.50  
% 7.68/1.50  fof(f72,plain,(
% 7.68/1.50    ~v1_xboole_0(sK1)),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f73,plain,(
% 7.68/1.50    ~v1_xboole_0(sK2)),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f79,plain,(
% 7.68/1.50    v1_funct_2(sK4,sK2,sK1)),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f2,axiom,(
% 7.68/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f37,plain,(
% 7.68/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.68/1.50    inference(nnf_transformation,[],[f2])).
% 7.68/1.50  
% 7.68/1.50  fof(f50,plain,(
% 7.68/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f37])).
% 7.68/1.50  
% 7.68/1.50  fof(f7,axiom,(
% 7.68/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f21,plain,(
% 7.68/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.68/1.50    inference(ennf_transformation,[],[f7])).
% 7.68/1.50  
% 7.68/1.50  fof(f22,plain,(
% 7.68/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.68/1.50    inference(flattening,[],[f21])).
% 7.68/1.50  
% 7.68/1.50  fof(f38,plain,(
% 7.68/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.68/1.50    inference(nnf_transformation,[],[f22])).
% 7.68/1.50  
% 7.68/1.50  fof(f56,plain,(
% 7.68/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f38])).
% 7.68/1.50  
% 7.68/1.50  fof(f77,plain,(
% 7.68/1.50    r1_subset_1(sK2,sK3)),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f75,plain,(
% 7.68/1.50    ~v1_xboole_0(sK3)),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f8,axiom,(
% 7.68/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f23,plain,(
% 7.68/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.68/1.50    inference(ennf_transformation,[],[f8])).
% 7.68/1.50  
% 7.68/1.50  fof(f58,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f23])).
% 7.68/1.50  
% 7.68/1.50  fof(f3,axiom,(
% 7.68/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f52,plain,(
% 7.68/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.68/1.50    inference(cnf_transformation,[],[f3])).
% 7.68/1.50  
% 7.68/1.50  fof(f1,axiom,(
% 7.68/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f49,plain,(
% 7.68/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f1])).
% 7.68/1.50  
% 7.68/1.50  fof(f51,plain,(
% 7.68/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.68/1.50    inference(cnf_transformation,[],[f37])).
% 7.68/1.50  
% 7.68/1.50  fof(f6,axiom,(
% 7.68/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.68/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f20,plain,(
% 7.68/1.50    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.68/1.50    inference(ennf_transformation,[],[f6])).
% 7.68/1.50  
% 7.68/1.50  fof(f55,plain,(
% 7.68/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f20])).
% 7.68/1.50  
% 7.68/1.50  fof(f74,plain,(
% 7.68/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f82,plain,(
% 7.68/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f65,plain,(
% 7.68/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f41])).
% 7.68/1.50  
% 7.68/1.50  fof(f89,plain,(
% 7.68/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.68/1.50    inference(equality_resolution,[],[f65])).
% 7.68/1.50  
% 7.68/1.50  fof(f84,plain,(
% 7.68/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.68/1.50    inference(cnf_transformation,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  cnf(c_23,negated_conjecture,
% 7.68/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.68/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_843,negated_conjecture,
% 7.68/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_23]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1345,plain,
% 7.68/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_15,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.68/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_849,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.68/1.50      | ~ v1_funct_1(X0_53)
% 7.68/1.50      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_15]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1340,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X2_53) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2523,plain,
% 7.68/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1345,c_1340]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25,negated_conjecture,
% 7.68/1.50      ( v1_funct_1(sK5) ),
% 7.68/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1791,plain,
% 7.68/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.68/1.50      | ~ v1_funct_1(sK5)
% 7.68/1.50      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_849]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2012,plain,
% 7.68/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.68/1.50      | ~ v1_funct_1(sK5)
% 7.68/1.50      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1791]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2954,plain,
% 7.68/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_2523,c_25,c_23,c_2012]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_30,negated_conjecture,
% 7.68/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.68/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_837,negated_conjecture,
% 7.68/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_30]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1351,plain,
% 7.68/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_837]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.68/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_852,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.68/1.50      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1337,plain,
% 7.68/1.50      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2383,plain,
% 7.68/1.50      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1351,c_1337]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_26,negated_conjecture,
% 7.68/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.68/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_840,negated_conjecture,
% 7.68/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_26]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1348,plain,
% 7.68/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2524,plain,
% 7.68/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 7.68/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1348,c_1340]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_28,negated_conjecture,
% 7.68/1.50      ( v1_funct_1(sK4) ),
% 7.68/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1796,plain,
% 7.68/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.68/1.50      | ~ v1_funct_1(sK4)
% 7.68/1.50      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_849]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2017,plain,
% 7.68/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ v1_funct_1(sK4)
% 7.68/1.50      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1796]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2959,plain,
% 7.68/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_2524,c_28,c_26,c_2017]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_17,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_1(X3)
% 7.68/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X1)
% 7.68/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_21,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_1(X3)
% 7.68/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_20,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_1(X3)
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_19,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_1(X3)
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_195,plain,
% 7.68/1.50      ( ~ v1_funct_1(X3)
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X1)
% 7.68/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_17,c_21,c_20,c_19]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_196,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_1(X3)
% 7.68/1.50      | v1_xboole_0(X1)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_195]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_830,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.68/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.68/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.68/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.68/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.68/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.68/1.50      | ~ v1_funct_1(X0_53)
% 7.68/1.50      | ~ v1_funct_1(X3_53)
% 7.68/1.50      | v1_xboole_0(X2_53)
% 7.68/1.50      | v1_xboole_0(X1_53)
% 7.68/1.50      | v1_xboole_0(X4_53)
% 7.68/1.50      | v1_xboole_0(X5_53)
% 7.68/1.50      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_196]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1358,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 7.68/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X3_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.68/1.50      | ~ v1_xboole_0(X1)
% 7.68/1.50      | v1_xboole_0(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_851,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.68/1.50      | ~ v1_xboole_0(X1_53)
% 7.68/1.50      | v1_xboole_0(X0_53) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1338,plain,
% 7.68/1.50      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1560,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
% 7.68/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X4_53) = iProver_top ),
% 7.68/1.50      inference(forward_subsumption_resolution,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_1358,c_1338]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6932,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.68/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.68/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.68/1.50      | v1_funct_1(sK4) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.68/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2959,c_1560]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_34,negated_conjecture,
% 7.68/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_37,plain,
% 7.68/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_33,negated_conjecture,
% 7.68/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.68/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38,plain,
% 7.68/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_43,plain,
% 7.68/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_27,negated_conjecture,
% 7.68/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_44,plain,
% 7.68/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_45,plain,
% 7.68/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25021,plain,
% 7.68/1.50      ( v1_funct_1(X1_53) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.68/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.68/1.50      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_6932,c_37,c_38,c_43,c_44,c_45]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25022,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.68/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_25021]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25043,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2383,c_25022]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2,plain,
% 7.68/1.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_252,plain,
% 7.68/1.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.68/1.50      inference(prop_impl,[status(thm)],[c_2]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_8,plain,
% 7.68/1.50      ( ~ r1_subset_1(X0,X1)
% 7.68/1.50      | r1_xboole_0(X0,X1)
% 7.68/1.50      | v1_xboole_0(X0)
% 7.68/1.50      | v1_xboole_0(X1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_29,negated_conjecture,
% 7.68/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.68/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_505,plain,
% 7.68/1.50      ( r1_xboole_0(X0,X1)
% 7.68/1.50      | v1_xboole_0(X0)
% 7.68/1.50      | v1_xboole_0(X1)
% 7.68/1.50      | sK3 != X1
% 7.68/1.50      | sK2 != X0 ),
% 7.68/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_506,plain,
% 7.68/1.50      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.68/1.50      inference(unflattening,[status(thm)],[c_505]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_31,negated_conjecture,
% 7.68/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.68/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_508,plain,
% 7.68/1.50      ( r1_xboole_0(sK2,sK3) ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_506,c_33,c_31]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_534,plain,
% 7.68/1.50      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 7.68/1.50      inference(resolution_lifted,[status(thm)],[c_252,c_508]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_535,plain,
% 7.68/1.50      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.68/1.50      inference(unflattening,[status(thm)],[c_534]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_828,plain,
% 7.68/1.50      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_535]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25140,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.68/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_53,k1_xboole_0)
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_25043,c_828]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25141,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_25140,c_2383]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_9,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_850,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.68/1.50      | v1_relat_1(X0_53) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1339,plain,
% 7.68/1.50      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.68/1.50      | v1_relat_1(X0_53) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2290,plain,
% 7.68/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1348,c_1339]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3,plain,
% 7.68/1.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_853,plain,
% 7.68/1.50      ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_0,plain,
% 7.68/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_854,plain,
% 7.68/1.50      ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1978,plain,
% 7.68/1.50      ( k3_xboole_0(k1_xboole_0,X0_53) = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_853,c_854]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1,plain,
% 7.68/1.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_250,plain,
% 7.68/1.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.68/1.50      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6,plain,
% 7.68/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.68/1.50      | ~ v1_relat_1(X1)
% 7.68/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_519,plain,
% 7.68/1.50      ( ~ v1_relat_1(X0)
% 7.68/1.50      | X1 != X2
% 7.68/1.50      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.68/1.50      | k3_xboole_0(X2,X3) != k1_xboole_0
% 7.68/1.50      | k1_relat_1(X0) != X3 ),
% 7.68/1.50      inference(resolution_lifted,[status(thm)],[c_250,c_6]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_520,plain,
% 7.68/1.50      ( ~ v1_relat_1(X0)
% 7.68/1.50      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.68/1.50      | k3_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0 ),
% 7.68/1.50      inference(unflattening,[status(thm)],[c_519]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_829,plain,
% 7.68/1.50      ( ~ v1_relat_1(X0_53)
% 7.68/1.50      | k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 7.68/1.50      | k3_xboole_0(X1_53,k1_relat_1(X0_53)) != k1_xboole_0 ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_520]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1359,plain,
% 7.68/1.50      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 7.68/1.50      | k3_xboole_0(X1_53,k1_relat_1(X0_53)) != k1_xboole_0
% 7.68/1.50      | v1_relat_1(X0_53) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3059,plain,
% 7.68/1.50      ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
% 7.68/1.50      | v1_relat_1(X0_53) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1978,c_1359]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3283,plain,
% 7.68/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2290,c_3059]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25142,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_25141,c_828,c_3283]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_32,negated_conjecture,
% 7.68/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.68/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_39,plain,
% 7.68/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_40,plain,
% 7.68/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_41,plain,
% 7.68/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25379,plain,
% 7.68/1.50      ( v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_25142,c_39,c_40,c_41]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25380,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_25379]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25390,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.68/1.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2954,c_25380]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2289,plain,
% 7.68/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1345,c_1339]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3282,plain,
% 7.68/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2289,c_3059]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25391,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.68/1.50      | k1_xboole_0 != k1_xboole_0
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_25390,c_3282]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25392,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(equality_resolution_simp,[status(thm)],[c_25391]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_847,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.68/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.68/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.68/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.68/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.68/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.68/1.50      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
% 7.68/1.50      | ~ v1_funct_1(X0_53)
% 7.68/1.50      | ~ v1_funct_1(X3_53)
% 7.68/1.50      | v1_xboole_0(X2_53)
% 7.68/1.50      | v1_xboole_0(X1_53)
% 7.68/1.50      | v1_xboole_0(X4_53)
% 7.68/1.50      | v1_xboole_0(X5_53) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_19]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1342,plain,
% 7.68/1.50      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X3_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X5_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1505,plain,
% 7.68/1.50      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X3_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top ),
% 7.68/1.50      inference(forward_subsumption_resolution,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_1342,c_1338]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4579,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.68/1.50      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X4_53) != iProver_top
% 7.68/1.50      | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
% 7.68/1.50      | v1_xboole_0(X3_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X2_53) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1505,c_1340]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_845,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.68/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.68/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.68/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.68/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.68/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.68/1.50      | ~ v1_funct_1(X0_53)
% 7.68/1.50      | ~ v1_funct_1(X3_53)
% 7.68/1.50      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
% 7.68/1.50      | v1_xboole_0(X2_53)
% 7.68/1.50      | v1_xboole_0(X1_53)
% 7.68/1.50      | v1_xboole_0(X4_53)
% 7.68/1.50      | v1_xboole_0(X5_53) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_21]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1344,plain,
% 7.68/1.50      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X3_53) != iProver_top
% 7.68/1.50      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.68/1.50      | v1_xboole_0(X5_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1453,plain,
% 7.68/1.50      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X3_53) != iProver_top
% 7.68/1.50      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.68/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top ),
% 7.68/1.50      inference(forward_subsumption_resolution,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_1344,c_1338]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10144,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.68/1.50      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X4_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X3_53) = iProver_top ),
% 7.68/1.50      inference(forward_subsumption_resolution,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_4579,c_1453]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10148,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.68/1.50      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1345,c_10144]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_46,plain,
% 7.68/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_24,negated_conjecture,
% 7.68/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_47,plain,
% 7.68/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10247,plain,
% 7.68/1.50      ( v1_funct_1(X2_53) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.68/1.50      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_10148,c_37,c_40,c_46,c_47]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10248,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.68/1.50      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_10247]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10261,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.68/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | v1_funct_1(sK4) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1348,c_10248]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10739,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_10261,c_38,c_43,c_44]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10748,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_1351,c_10739]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10753,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_10748,c_39]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25393,plain,
% 7.68/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_25392,c_10753]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_18,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_1(X3)
% 7.68/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X1)
% 7.68/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.68/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_188,plain,
% 7.68/1.50      ( ~ v1_funct_1(X3)
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X1)
% 7.68/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_18,c_21,c_20,c_19]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_189,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.68/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_1(X3)
% 7.68/1.50      | v1_xboole_0(X1)
% 7.68/1.50      | v1_xboole_0(X2)
% 7.68/1.50      | v1_xboole_0(X4)
% 7.68/1.50      | v1_xboole_0(X5)
% 7.68/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_188]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_831,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.68/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.68/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.68/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.68/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.68/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.68/1.50      | ~ v1_funct_1(X0_53)
% 7.68/1.50      | ~ v1_funct_1(X3_53)
% 7.68/1.50      | v1_xboole_0(X2_53)
% 7.68/1.50      | v1_xboole_0(X1_53)
% 7.68/1.50      | v1_xboole_0(X4_53)
% 7.68/1.50      | v1_xboole_0(X5_53)
% 7.68/1.50      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_189]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1357,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 7.68/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X3_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1532,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
% 7.68/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.68/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.68/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.68/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.68/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(X4_53) = iProver_top ),
% 7.68/1.50      inference(forward_subsumption_resolution,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_1357,c_1338]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5760,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.68/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.68/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.68/1.50      | v1_funct_1(sK4) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.68/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.68/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2959,c_1532]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_14259,plain,
% 7.68/1.50      ( v1_funct_1(X1_53) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.68/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.68/1.50      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_5760,c_37,c_38,c_43,c_44,c_45]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_14260,plain,
% 7.68/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.68/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.68/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.68/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_14259]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_14281,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2383,c_14260]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_14378,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.68/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_53,k1_xboole_0)
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_14281,c_828]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_14379,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_14378,c_2383]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_14380,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_14379,c_828,c_3283]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_15393,plain,
% 7.68/1.50      ( v1_funct_1(X0_53) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_14380,c_39,c_40,c_41]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_15394,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.68/1.50      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_15393]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_15404,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.68/1.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2954,c_15394]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_15405,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.68/1.50      | k1_xboole_0 != k1_xboole_0
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_15404,c_3282]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_15406,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(equality_resolution_simp,[status(thm)],[c_15405]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_15407,plain,
% 7.68/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.68/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.68/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_15406,c_10753]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_22,negated_conjecture,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.68/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.68/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_844,negated_conjecture,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.68/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.68/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2642,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.68/1.50      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_2383,c_844]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2643,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.68/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_2642,c_828]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3049,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.68/1.50      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_2643,c_2954,c_2959]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3780,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.68/1.50      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_3282,c_3049]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4724,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_3780,c_3283]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4725,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.68/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_4724]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10757,plain,
% 7.68/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.68/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_10753,c_4725]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_10758,plain,
% 7.68/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.68/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_10757,c_10753]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_48,plain,
% 7.68/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(contradiction,plain,
% 7.68/1.50      ( $false ),
% 7.68/1.50      inference(minisat,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_25393,c_15407,c_10758,c_48,c_47,c_46]) ).
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.68/1.50  
% 7.68/1.50  ------                               Statistics
% 7.68/1.50  
% 7.68/1.50  ------ Selected
% 7.68/1.50  
% 7.68/1.50  total_time:                             0.985
% 7.68/1.50  
%------------------------------------------------------------------------------
