%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:35 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :  254 (3029 expanded)
%              Number of clauses        :  165 ( 861 expanded)
%              Number of leaves         :   23 (1108 expanded)
%              Depth                    :   27
%              Number of atoms          : 1241 (35748 expanded)
%              Number of equality atoms :  460 (8350 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f43,f53,f52,f51,f50,f49,f48])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f79,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_490,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1155,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1131,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_1981,plain,
    ( k9_subset_1(sK0,X0_54,sK3) = k3_xboole_0(X0_54,sK3) ),
    inference(superposition,[status(thm)],[c_1155,c_1131])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_494,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1151,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1143,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_4634,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1143])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1683,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_1968,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_4712,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4634,c_30,c_28,c_1968])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_497,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1148,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_4633,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1143])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1678,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_1963,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_4706,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4633,c_27,c_25,c_1963])).

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
    inference(cnf_transformation,[],[f97])).

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
    inference(cnf_transformation,[],[f76])).

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
    inference(cnf_transformation,[],[f77])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_292,plain,
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

cnf(c_293,plain,
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
    inference(renaming,[status(thm)],[c_292])).

cnf(c_483,plain,
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
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_1162,plain,
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
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_8514,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4706,c_1162])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_42,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_48,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_49,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_13239,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8514,c_39,c_42,c_48,c_49,c_50])).

cnf(c_13240,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_13239])).

cnf(c_13255,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4712,c_13240])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_46,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13535,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13255,c_40,c_45,c_46,c_47])).

cnf(c_13536,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_13535])).

cnf(c_13546,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_13536])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1138,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_2359,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1138])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_518,plain,
    ( r1_xboole_0(X0_54,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1130,plain,
    ( r1_xboole_0(X0_54,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_519,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | r1_xboole_0(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1129,plain,
    ( r1_xboole_0(X0_54,X1_54) != iProver_top
    | r1_xboole_0(X1_54,X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_2352,plain,
    ( r1_xboole_0(k1_xboole_0,X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1129])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_516,plain,
    ( ~ r1_xboole_0(X0_54,k1_relat_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | k7_relat_1(X1_54,X0_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1132,plain,
    ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(X1_54,k1_relat_1(X0_54)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_6584,plain,
    ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_1132])).

cnf(c_7863,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2359,c_6584])).

cnf(c_2360,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1138])).

cnf(c_31,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_491,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1154,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_10,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_509,plain,
    ( ~ r1_subset_1(X0_54,X1_54)
    | r1_xboole_0(X0_54,X1_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1137,plain,
    ( r1_subset_1(X0_54,X1_54) != iProver_top
    | r1_xboole_0(X0_54,X1_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_3288,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1137])).

cnf(c_44,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1596,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_1597,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1596])).

cnf(c_3625,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3288,c_40,c_42,c_44,c_1597])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_515,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | ~ v1_relat_1(X2_54)
    | k7_relat_1(k7_relat_1(X2_54,X0_54),X1_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1133,plain,
    ( k7_relat_1(k7_relat_1(X0_54,X1_54),X2_54) = k1_xboole_0
    | r1_xboole_0(X1_54,X2_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_3632,plain,
    ( k7_relat_1(k7_relat_1(X0_54,sK2),sK3) = k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3625,c_1133])).

cnf(c_3870,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2360,c_3632])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_507,plain,
    ( v4_relat_1(X0_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1139,plain,
    ( v4_relat_1(X0_54,X1_54) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_2456,plain,
    ( v4_relat_1(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1139])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_514,plain,
    ( ~ v4_relat_1(X0_54,X1_54)
    | ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1134,plain,
    ( k7_relat_1(X0_54,X1_54) = X0_54
    | v4_relat_1(X0_54,X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_3295,plain,
    ( k7_relat_1(sK4,sK2) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_1134])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_1593,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_1836,plain,
    ( ~ v4_relat_1(sK4,X0_54)
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0_54) = sK4 ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_1843,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_3863,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3295,c_28,c_1561,c_1593,c_1843])).

cnf(c_3872,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3870,c_3863])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_506,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | v1_partfun1(X0_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | v1_xboole_0(X2_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1140,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_partfun1(X0_54,X1_54) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_4286,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1140])).

cnf(c_1693,plain,
    ( ~ v1_funct_2(sK4,X0_54,X1_54)
    | v1_partfun1(sK4,X0_54)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_54) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_1976,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_1977,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1976])).

cnf(c_5070,plain,
    ( v1_partfun1(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4286,c_39,c_45,c_46,c_47,c_1977])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_504,plain,
    ( ~ v1_partfun1(X0_54,X1_54)
    | ~ v4_relat_1(X0_54,X1_54)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1142,plain,
    ( k1_relat_1(X0_54) = X1_54
    | v1_partfun1(X0_54,X1_54) != iProver_top
    | v4_relat_1(X0_54,X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_5075,plain,
    ( k1_relat_1(sK4) = sK2
    | v4_relat_1(sK4,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5070,c_1142])).

cnf(c_1835,plain,
    ( ~ v1_partfun1(sK4,X0_54)
    | ~ v4_relat_1(sK4,X0_54)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = X0_54 ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1847,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_5299,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5075,c_36,c_30,c_29,c_28,c_1561,c_1593,c_1847,c_1976])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_511,plain,
    ( ~ v1_relat_1(X0_54)
    | k1_relat_1(k7_relat_1(X0_54,X1_54)) = k3_xboole_0(k1_relat_1(X0_54),X1_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1135,plain,
    ( k1_relat_1(k7_relat_1(X0_54,X1_54)) = k3_xboole_0(k1_relat_1(X0_54),X1_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_2550,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0_54)) = k3_xboole_0(k1_relat_1(sK4),X0_54) ),
    inference(superposition,[status(thm)],[c_2360,c_1135])).

cnf(c_5302,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0_54)) = k3_xboole_0(sK2,X0_54) ),
    inference(demodulation,[status(thm)],[c_5299,c_2550])).

cnf(c_11631,plain,
    ( k3_xboole_0(sK2,sK3) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3872,c_5302])).

cnf(c_7,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_512,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_11648,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11631,c_512])).

cnf(c_13547,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13546,c_7863,c_11648])).

cnf(c_13548,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13547,c_1981])).

cnf(c_7864,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2360,c_6584])).

cnf(c_13549,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13548,c_7864,c_11648])).

cnf(c_13550,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13549])).

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
    inference(cnf_transformation,[],[f96])).

cnf(c_283,plain,
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

cnf(c_284,plain,
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
    inference(renaming,[status(thm)],[c_283])).

cnf(c_484,plain,
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
    inference(subtyping,[status(esa)],[c_284])).

cnf(c_1161,plain,
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
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_7394,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4706,c_1161])).

cnf(c_8309,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7394,c_39,c_42,c_48,c_49,c_50])).

cnf(c_8310,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_8309])).

cnf(c_8325,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4712,c_8310])).

cnf(c_9287,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8325,c_40,c_45,c_46,c_47])).

cnf(c_9288,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_9287])).

cnf(c_9298,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_9288])).

cnf(c_9299,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9298,c_1981])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_9300,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9299])).

cnf(c_9397,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9299,c_37,c_34,c_32,c_9300])).

cnf(c_9398,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_9397])).

cnf(c_11995,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11648,c_9398])).

cnf(c_12006,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11995,c_7863,c_7864])).

cnf(c_12007,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_12006])).

cnf(c_24,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_498,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2183,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1981,c_498])).

cnf(c_4710,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4706,c_2183])).

cnf(c_4906,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4710,c_4712])).

cnf(c_11996,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11648,c_4906])).

cnf(c_12000,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11996,c_7863,c_7864])).

cnf(c_12001,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_12000])).

cnf(c_12009,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12007,c_12001])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13550,c_12009,c_43,c_41,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:21:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.50/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.50/1.50  
% 7.50/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.50/1.50  
% 7.50/1.50  ------  iProver source info
% 7.50/1.50  
% 7.50/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.50/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.50/1.50  git: non_committed_changes: false
% 7.50/1.50  git: last_make_outside_of_git: false
% 7.50/1.50  
% 7.50/1.50  ------ 
% 7.50/1.50  ------ Parsing...
% 7.50/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.50/1.50  
% 7.50/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.50/1.50  
% 7.50/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.50/1.50  
% 7.50/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.50/1.50  ------ Proving...
% 7.50/1.50  ------ Problem Properties 
% 7.50/1.50  
% 7.50/1.50  
% 7.50/1.50  clauses                                 37
% 7.50/1.50  conjectures                             14
% 7.50/1.50  EPR                                     13
% 7.50/1.50  Horn                                    28
% 7.50/1.50  unary                                   16
% 7.50/1.50  binary                                  5
% 7.50/1.50  lits                                    145
% 7.50/1.50  lits eq                                 18
% 7.50/1.50  fd_pure                                 0
% 7.50/1.50  fd_pseudo                               0
% 7.50/1.50  fd_cond                                 0
% 7.50/1.50  fd_pseudo_cond                          1
% 7.50/1.50  AC symbols                              0
% 7.50/1.50  
% 7.50/1.50  ------ Input Options Time Limit: Unbounded
% 7.50/1.50  
% 7.50/1.50  
% 7.50/1.50  ------ 
% 7.50/1.50  Current options:
% 7.50/1.50  ------ 
% 7.50/1.50  
% 7.50/1.50  
% 7.50/1.50  
% 7.50/1.50  
% 7.50/1.50  ------ Proving...
% 7.50/1.50  
% 7.50/1.50  
% 7.50/1.50  % SZS status Theorem for theBenchmark.p
% 7.50/1.50  
% 7.50/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.50/1.50  
% 7.50/1.50  fof(f17,conjecture,(
% 7.50/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f18,negated_conjecture,(
% 7.50/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.50/1.50    inference(negated_conjecture,[],[f17])).
% 7.50/1.50  
% 7.50/1.50  fof(f42,plain,(
% 7.50/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.50/1.50    inference(ennf_transformation,[],[f18])).
% 7.50/1.50  
% 7.50/1.50  fof(f43,plain,(
% 7.50/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.50/1.50    inference(flattening,[],[f42])).
% 7.50/1.50  
% 7.50/1.50  fof(f53,plain,(
% 7.50/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.50/1.50    introduced(choice_axiom,[])).
% 7.50/1.50  
% 7.50/1.50  fof(f52,plain,(
% 7.50/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.50/1.50    introduced(choice_axiom,[])).
% 7.50/1.50  
% 7.50/1.50  fof(f51,plain,(
% 7.50/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.50/1.50    introduced(choice_axiom,[])).
% 7.50/1.50  
% 7.50/1.50  fof(f50,plain,(
% 7.50/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.50/1.50    introduced(choice_axiom,[])).
% 7.50/1.50  
% 7.50/1.50  fof(f49,plain,(
% 7.50/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.50/1.50    introduced(choice_axiom,[])).
% 7.50/1.50  
% 7.50/1.50  fof(f48,plain,(
% 7.50/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.50/1.50    introduced(choice_axiom,[])).
% 7.50/1.50  
% 7.50/1.50  fof(f54,plain,(
% 7.50/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.50/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f43,f53,f52,f51,f50,f49,f48])).
% 7.50/1.50  
% 7.50/1.50  fof(f84,plain,(
% 7.50/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f3,axiom,(
% 7.50/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f21,plain,(
% 7.50/1.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.50/1.50    inference(ennf_transformation,[],[f3])).
% 7.50/1.50  
% 7.50/1.50  fof(f57,plain,(
% 7.50/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.50/1.50    inference(cnf_transformation,[],[f21])).
% 7.50/1.50  
% 7.50/1.50  fof(f88,plain,(
% 7.50/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f14,axiom,(
% 7.50/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f36,plain,(
% 7.50/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.50/1.50    inference(ennf_transformation,[],[f14])).
% 7.50/1.50  
% 7.50/1.50  fof(f37,plain,(
% 7.50/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.50/1.50    inference(flattening,[],[f36])).
% 7.50/1.50  
% 7.50/1.50  fof(f72,plain,(
% 7.50/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f37])).
% 7.50/1.50  
% 7.50/1.50  fof(f86,plain,(
% 7.50/1.50    v1_funct_1(sK4)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f91,plain,(
% 7.50/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f89,plain,(
% 7.50/1.50    v1_funct_1(sK5)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f15,axiom,(
% 7.50/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f38,plain,(
% 7.50/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.50/1.50    inference(ennf_transformation,[],[f15])).
% 7.50/1.50  
% 7.50/1.50  fof(f39,plain,(
% 7.50/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.50/1.50    inference(flattening,[],[f38])).
% 7.50/1.50  
% 7.50/1.50  fof(f46,plain,(
% 7.50/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.50/1.50    inference(nnf_transformation,[],[f39])).
% 7.50/1.50  
% 7.50/1.50  fof(f47,plain,(
% 7.50/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.50/1.50    inference(flattening,[],[f46])).
% 7.50/1.50  
% 7.50/1.50  fof(f73,plain,(
% 7.50/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f47])).
% 7.50/1.50  
% 7.50/1.50  fof(f97,plain,(
% 7.50/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.50/1.50    inference(equality_resolution,[],[f73])).
% 7.50/1.50  
% 7.50/1.50  fof(f16,axiom,(
% 7.50/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f40,plain,(
% 7.50/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.50/1.50    inference(ennf_transformation,[],[f16])).
% 7.50/1.50  
% 7.50/1.50  fof(f41,plain,(
% 7.50/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.50/1.50    inference(flattening,[],[f40])).
% 7.50/1.50  
% 7.50/1.50  fof(f76,plain,(
% 7.50/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f41])).
% 7.50/1.50  
% 7.50/1.50  fof(f77,plain,(
% 7.50/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f41])).
% 7.50/1.50  
% 7.50/1.50  fof(f78,plain,(
% 7.50/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f41])).
% 7.50/1.50  
% 7.50/1.50  fof(f80,plain,(
% 7.50/1.50    ~v1_xboole_0(sK1)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f83,plain,(
% 7.50/1.50    ~v1_xboole_0(sK3)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f90,plain,(
% 7.50/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f81,plain,(
% 7.50/1.50    ~v1_xboole_0(sK2)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f87,plain,(
% 7.50/1.50    v1_funct_2(sK4,sK2,sK1)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f10,axiom,(
% 7.50/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f30,plain,(
% 7.50/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.50/1.50    inference(ennf_transformation,[],[f10])).
% 7.50/1.50  
% 7.50/1.50  fof(f66,plain,(
% 7.50/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.50/1.50    inference(cnf_transformation,[],[f30])).
% 7.50/1.50  
% 7.50/1.50  fof(f2,axiom,(
% 7.50/1.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f56,plain,(
% 7.50/1.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f2])).
% 7.50/1.50  
% 7.50/1.50  fof(f1,axiom,(
% 7.50/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f20,plain,(
% 7.50/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.50/1.50    inference(ennf_transformation,[],[f1])).
% 7.50/1.50  
% 7.50/1.50  fof(f55,plain,(
% 7.50/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f20])).
% 7.50/1.50  
% 7.50/1.50  fof(f4,axiom,(
% 7.50/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f22,plain,(
% 7.50/1.50    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.50/1.50    inference(ennf_transformation,[],[f4])).
% 7.50/1.50  
% 7.50/1.50  fof(f58,plain,(
% 7.50/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f22])).
% 7.50/1.50  
% 7.50/1.50  fof(f85,plain,(
% 7.50/1.50    r1_subset_1(sK2,sK3)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f9,axiom,(
% 7.50/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f28,plain,(
% 7.50/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.50/1.50    inference(ennf_transformation,[],[f9])).
% 7.50/1.50  
% 7.50/1.50  fof(f29,plain,(
% 7.50/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.50/1.50    inference(flattening,[],[f28])).
% 7.50/1.50  
% 7.50/1.50  fof(f44,plain,(
% 7.50/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.50/1.50    inference(nnf_transformation,[],[f29])).
% 7.50/1.50  
% 7.50/1.50  fof(f64,plain,(
% 7.50/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f44])).
% 7.50/1.50  
% 7.50/1.50  fof(f5,axiom,(
% 7.50/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f23,plain,(
% 7.50/1.50    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.50/1.50    inference(ennf_transformation,[],[f5])).
% 7.50/1.50  
% 7.50/1.50  fof(f24,plain,(
% 7.50/1.50    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.50/1.50    inference(flattening,[],[f23])).
% 7.50/1.50  
% 7.50/1.50  fof(f59,plain,(
% 7.50/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f24])).
% 7.50/1.50  
% 7.50/1.50  fof(f11,axiom,(
% 7.50/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f19,plain,(
% 7.50/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.50/1.50    inference(pure_predicate_removal,[],[f11])).
% 7.50/1.50  
% 7.50/1.50  fof(f31,plain,(
% 7.50/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.50/1.50    inference(ennf_transformation,[],[f19])).
% 7.50/1.50  
% 7.50/1.50  fof(f67,plain,(
% 7.50/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.50/1.50    inference(cnf_transformation,[],[f31])).
% 7.50/1.50  
% 7.50/1.50  fof(f6,axiom,(
% 7.50/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f25,plain,(
% 7.50/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.50/1.50    inference(ennf_transformation,[],[f6])).
% 7.50/1.50  
% 7.50/1.50  fof(f26,plain,(
% 7.50/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.50/1.50    inference(flattening,[],[f25])).
% 7.50/1.50  
% 7.50/1.50  fof(f60,plain,(
% 7.50/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f26])).
% 7.50/1.50  
% 7.50/1.50  fof(f12,axiom,(
% 7.50/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f32,plain,(
% 7.50/1.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.50/1.50    inference(ennf_transformation,[],[f12])).
% 7.50/1.50  
% 7.50/1.50  fof(f33,plain,(
% 7.50/1.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.50/1.50    inference(flattening,[],[f32])).
% 7.50/1.50  
% 7.50/1.50  fof(f69,plain,(
% 7.50/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f33])).
% 7.50/1.50  
% 7.50/1.50  fof(f13,axiom,(
% 7.50/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f34,plain,(
% 7.50/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.50/1.50    inference(ennf_transformation,[],[f13])).
% 7.50/1.50  
% 7.50/1.50  fof(f35,plain,(
% 7.50/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.50/1.50    inference(flattening,[],[f34])).
% 7.50/1.50  
% 7.50/1.50  fof(f45,plain,(
% 7.50/1.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.50/1.50    inference(nnf_transformation,[],[f35])).
% 7.50/1.50  
% 7.50/1.50  fof(f70,plain,(
% 7.50/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f45])).
% 7.50/1.50  
% 7.50/1.50  fof(f8,axiom,(
% 7.50/1.50    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f27,plain,(
% 7.50/1.50    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.50/1.50    inference(ennf_transformation,[],[f8])).
% 7.50/1.50  
% 7.50/1.50  fof(f63,plain,(
% 7.50/1.50    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f27])).
% 7.50/1.50  
% 7.50/1.50  fof(f7,axiom,(
% 7.50/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.50/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.50/1.50  
% 7.50/1.50  fof(f61,plain,(
% 7.50/1.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.50/1.50    inference(cnf_transformation,[],[f7])).
% 7.50/1.50  
% 7.50/1.50  fof(f74,plain,(
% 7.50/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.50/1.50    inference(cnf_transformation,[],[f47])).
% 7.50/1.50  
% 7.50/1.50  fof(f96,plain,(
% 7.50/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.50/1.50    inference(equality_resolution,[],[f74])).
% 7.50/1.50  
% 7.50/1.50  fof(f79,plain,(
% 7.50/1.50    ~v1_xboole_0(sK0)),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f82,plain,(
% 7.50/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  fof(f92,plain,(
% 7.50/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.50/1.50    inference(cnf_transformation,[],[f54])).
% 7.50/1.50  
% 7.50/1.50  cnf(c_32,negated_conjecture,
% 7.50/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.50/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_490,negated_conjecture,
% 7.50/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_32]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1155,plain,
% 7.50/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_2,plain,
% 7.50/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.50/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.50/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_517,plain,
% 7.50/1.50      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.50/1.50      | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1131,plain,
% 7.50/1.50      ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
% 7.50/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1981,plain,
% 7.50/1.50      ( k9_subset_1(sK0,X0_54,sK3) = k3_xboole_0(X0_54,sK3) ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1155,c_1131]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_28,negated_conjecture,
% 7.50/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.50/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_494,negated_conjecture,
% 7.50/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_28]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1151,plain,
% 7.50/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_17,plain,
% 7.50/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.50/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_503,plain,
% 7.50/1.50      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.50/1.50      | ~ v1_funct_1(X0_54)
% 7.50/1.50      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1143,plain,
% 7.50/1.50      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.50/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.50/1.50      | v1_funct_1(X2_54) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_4634,plain,
% 7.50/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 7.50/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1151,c_1143]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_30,negated_conjecture,
% 7.50/1.50      ( v1_funct_1(sK4) ),
% 7.50/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1683,plain,
% 7.50/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.50/1.50      | ~ v1_funct_1(sK4)
% 7.50/1.50      | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_503]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1968,plain,
% 7.50/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.50/1.50      | ~ v1_funct_1(sK4)
% 7.50/1.50      | k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_1683]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_4712,plain,
% 7.50/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_4634,c_30,c_28,c_1968]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_25,negated_conjecture,
% 7.50/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.50/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_497,negated_conjecture,
% 7.50/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_25]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1148,plain,
% 7.50/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_4633,plain,
% 7.50/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
% 7.50/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1148,c_1143]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_27,negated_conjecture,
% 7.50/1.50      ( v1_funct_1(sK5) ),
% 7.50/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1678,plain,
% 7.50/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.50/1.50      | ~ v1_funct_1(sK5)
% 7.50/1.50      | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_503]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1963,plain,
% 7.50/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.50/1.50      | ~ v1_funct_1(sK5)
% 7.50/1.50      | k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_1678]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_4706,plain,
% 7.50/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_4633,c_27,c_25,c_1963]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_20,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_1(X3)
% 7.50/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X1)
% 7.50/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.50/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_23,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_1(X3)
% 7.50/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X1) ),
% 7.50/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_22,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_1(X3)
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X1) ),
% 7.50/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_21,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_1(X3)
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X1) ),
% 7.50/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_292,plain,
% 7.50/1.50      ( ~ v1_funct_1(X3)
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X1)
% 7.50/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_20,c_23,c_22,c_21]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_293,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_1(X3)
% 7.50/1.50      | v1_xboole_0(X1)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.50/1.50      inference(renaming,[status(thm)],[c_292]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_483,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.50/1.50      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.50/1.50      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.50/1.50      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.50/1.50      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.50/1.50      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.50/1.50      | ~ v1_funct_1(X0_54)
% 7.50/1.50      | ~ v1_funct_1(X3_54)
% 7.50/1.50      | v1_xboole_0(X1_54)
% 7.50/1.50      | v1_xboole_0(X2_54)
% 7.50/1.50      | v1_xboole_0(X4_54)
% 7.50/1.50      | v1_xboole_0(X5_54)
% 7.50/1.50      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_293]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1162,plain,
% 7.50/1.50      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 7.50/1.50      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.50/1.50      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.50/1.50      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.50/1.50      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.50/1.50      | v1_funct_1(X2_54) != iProver_top
% 7.50/1.50      | v1_funct_1(X5_54) != iProver_top
% 7.50/1.50      | v1_xboole_0(X3_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X1_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X4_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_8514,plain,
% 7.50/1.50      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.50/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.50/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.50/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | v1_funct_1(X1_54) != iProver_top
% 7.50/1.50      | v1_funct_1(sK5) != iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X2_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_4706,c_1162]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_36,negated_conjecture,
% 7.50/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.50/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_39,plain,
% 7.50/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_33,negated_conjecture,
% 7.50/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.50/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_42,plain,
% 7.50/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_48,plain,
% 7.50/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_26,negated_conjecture,
% 7.50/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.50/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_49,plain,
% 7.50/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_50,plain,
% 7.50/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13239,plain,
% 7.50/1.50      ( v1_funct_1(X1_54) != iProver_top
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.50/1.50      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.50/1.50      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X2_54) = iProver_top ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_8514,c_39,c_42,c_48,c_49,c_50]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13240,plain,
% 7.50/1.50      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.50/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | v1_funct_1(X1_54) != iProver_top
% 7.50/1.50      | v1_xboole_0(X2_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.50/1.50      inference(renaming,[status(thm)],[c_13239]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13255,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.50/1.50      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.50/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.50/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | v1_funct_1(sK4) != iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_4712,c_13240]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_35,negated_conjecture,
% 7.50/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.50/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_40,plain,
% 7.50/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_45,plain,
% 7.50/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_29,negated_conjecture,
% 7.50/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.50/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_46,plain,
% 7.50/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_47,plain,
% 7.50/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13535,plain,
% 7.50/1.50      ( v1_xboole_0(X0_54) = iProver_top
% 7.50/1.50      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.50/1.50      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_13255,c_40,c_45,c_46,c_47]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13536,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.50/1.50      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.50/1.50      inference(renaming,[status(thm)],[c_13535]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13546,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.50/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1981,c_13536]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_11,plain,
% 7.50/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | v1_relat_1(X0) ),
% 7.50/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_508,plain,
% 7.50/1.50      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.50/1.50      | v1_relat_1(X0_54) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1138,plain,
% 7.50/1.50      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.50/1.50      | v1_relat_1(X0_54) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_2359,plain,
% 7.50/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1148,c_1138]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1,plain,
% 7.50/1.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.50/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_518,plain,
% 7.50/1.50      ( r1_xboole_0(X0_54,k1_xboole_0) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1130,plain,
% 7.50/1.50      ( r1_xboole_0(X0_54,k1_xboole_0) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_0,plain,
% 7.50/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.50/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_519,plain,
% 7.50/1.50      ( ~ r1_xboole_0(X0_54,X1_54) | r1_xboole_0(X1_54,X0_54) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1129,plain,
% 7.50/1.50      ( r1_xboole_0(X0_54,X1_54) != iProver_top
% 7.50/1.50      | r1_xboole_0(X1_54,X0_54) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_2352,plain,
% 7.50/1.50      ( r1_xboole_0(k1_xboole_0,X0_54) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1130,c_1129]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_3,plain,
% 7.50/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.50/1.50      | ~ v1_relat_1(X1)
% 7.50/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.50/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_516,plain,
% 7.50/1.50      ( ~ r1_xboole_0(X0_54,k1_relat_1(X1_54))
% 7.50/1.50      | ~ v1_relat_1(X1_54)
% 7.50/1.50      | k7_relat_1(X1_54,X0_54) = k1_xboole_0 ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1132,plain,
% 7.50/1.50      ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 7.50/1.50      | r1_xboole_0(X1_54,k1_relat_1(X0_54)) != iProver_top
% 7.50/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_6584,plain,
% 7.50/1.50      ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
% 7.50/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_2352,c_1132]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_7863,plain,
% 7.50/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_2359,c_6584]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_2360,plain,
% 7.50/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1151,c_1138]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_31,negated_conjecture,
% 7.50/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.50/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_491,negated_conjecture,
% 7.50/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_31]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1154,plain,
% 7.50/1.50      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_10,plain,
% 7.50/1.50      ( ~ r1_subset_1(X0,X1)
% 7.50/1.50      | r1_xboole_0(X0,X1)
% 7.50/1.50      | v1_xboole_0(X0)
% 7.50/1.50      | v1_xboole_0(X1) ),
% 7.50/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_509,plain,
% 7.50/1.50      ( ~ r1_subset_1(X0_54,X1_54)
% 7.50/1.50      | r1_xboole_0(X0_54,X1_54)
% 7.50/1.50      | v1_xboole_0(X1_54)
% 7.50/1.50      | v1_xboole_0(X0_54) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1137,plain,
% 7.50/1.50      ( r1_subset_1(X0_54,X1_54) != iProver_top
% 7.50/1.50      | r1_xboole_0(X0_54,X1_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X1_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_3288,plain,
% 7.50/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1154,c_1137]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_44,plain,
% 7.50/1.50      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1596,plain,
% 7.50/1.50      ( ~ r1_subset_1(sK2,sK3)
% 7.50/1.50      | r1_xboole_0(sK2,sK3)
% 7.50/1.50      | v1_xboole_0(sK3)
% 7.50/1.50      | v1_xboole_0(sK2) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_509]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1597,plain,
% 7.50/1.50      ( r1_subset_1(sK2,sK3) != iProver_top
% 7.50/1.50      | r1_xboole_0(sK2,sK3) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_1596]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_3625,plain,
% 7.50/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_3288,c_40,c_42,c_44,c_1597]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_4,plain,
% 7.50/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.50/1.50      | ~ v1_relat_1(X2)
% 7.50/1.50      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.50/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_515,plain,
% 7.50/1.50      ( ~ r1_xboole_0(X0_54,X1_54)
% 7.50/1.50      | ~ v1_relat_1(X2_54)
% 7.50/1.50      | k7_relat_1(k7_relat_1(X2_54,X0_54),X1_54) = k1_xboole_0 ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1133,plain,
% 7.50/1.50      ( k7_relat_1(k7_relat_1(X0_54,X1_54),X2_54) = k1_xboole_0
% 7.50/1.50      | r1_xboole_0(X1_54,X2_54) != iProver_top
% 7.50/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_3632,plain,
% 7.50/1.50      ( k7_relat_1(k7_relat_1(X0_54,sK2),sK3) = k1_xboole_0
% 7.50/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_3625,c_1133]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_3870,plain,
% 7.50/1.50      ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_2360,c_3632]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_12,plain,
% 7.50/1.50      ( v4_relat_1(X0,X1)
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.50/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_507,plain,
% 7.50/1.50      ( v4_relat_1(X0_54,X1_54)
% 7.50/1.50      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1139,plain,
% 7.50/1.50      ( v4_relat_1(X0_54,X1_54) = iProver_top
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_2456,plain,
% 7.50/1.50      ( v4_relat_1(sK4,sK2) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1151,c_1139]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_5,plain,
% 7.50/1.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.50/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_514,plain,
% 7.50/1.50      ( ~ v4_relat_1(X0_54,X1_54)
% 7.50/1.50      | ~ v1_relat_1(X0_54)
% 7.50/1.50      | k7_relat_1(X0_54,X1_54) = X0_54 ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1134,plain,
% 7.50/1.50      ( k7_relat_1(X0_54,X1_54) = X0_54
% 7.50/1.50      | v4_relat_1(X0_54,X1_54) != iProver_top
% 7.50/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_3295,plain,
% 7.50/1.50      ( k7_relat_1(sK4,sK2) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_2456,c_1134]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1561,plain,
% 7.50/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.50/1.50      | v1_relat_1(sK4) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_508]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1593,plain,
% 7.50/1.50      ( v4_relat_1(sK4,sK2)
% 7.50/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_507]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1836,plain,
% 7.50/1.50      ( ~ v4_relat_1(sK4,X0_54)
% 7.50/1.50      | ~ v1_relat_1(sK4)
% 7.50/1.50      | k7_relat_1(sK4,X0_54) = sK4 ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_514]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1843,plain,
% 7.50/1.50      ( ~ v4_relat_1(sK4,sK2)
% 7.50/1.50      | ~ v1_relat_1(sK4)
% 7.50/1.50      | k7_relat_1(sK4,sK2) = sK4 ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_1836]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_3863,plain,
% 7.50/1.50      ( k7_relat_1(sK4,sK2) = sK4 ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_3295,c_28,c_1561,c_1593,c_1843]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_3872,plain,
% 7.50/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.50/1.50      inference(light_normalisation,[status(thm)],[c_3870,c_3863]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | v1_partfun1(X0,X1)
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | v1_xboole_0(X2) ),
% 7.50/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_506,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.50/1.50      | v1_partfun1(X0_54,X1_54)
% 7.50/1.50      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.50/1.50      | ~ v1_funct_1(X0_54)
% 7.50/1.50      | v1_xboole_0(X2_54) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1140,plain,
% 7.50/1.50      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.50/1.50      | v1_partfun1(X0_54,X1_54) = iProver_top
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.50/1.50      | v1_funct_1(X0_54) != iProver_top
% 7.50/1.50      | v1_xboole_0(X2_54) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_4286,plain,
% 7.50/1.50      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.50/1.50      | v1_partfun1(sK4,sK2) = iProver_top
% 7.50/1.50      | v1_funct_1(sK4) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1151,c_1140]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1693,plain,
% 7.50/1.50      ( ~ v1_funct_2(sK4,X0_54,X1_54)
% 7.50/1.50      | v1_partfun1(sK4,X0_54)
% 7.50/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.50/1.50      | ~ v1_funct_1(sK4)
% 7.50/1.50      | v1_xboole_0(X1_54) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_506]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1976,plain,
% 7.50/1.50      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.50/1.50      | v1_partfun1(sK4,sK2)
% 7.50/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.50/1.50      | ~ v1_funct_1(sK4)
% 7.50/1.50      | v1_xboole_0(sK1) ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_1693]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1977,plain,
% 7.50/1.50      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.50/1.50      | v1_partfun1(sK4,sK2) = iProver_top
% 7.50/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.50/1.50      | v1_funct_1(sK4) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_1976]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_5070,plain,
% 7.50/1.50      ( v1_partfun1(sK4,sK2) = iProver_top ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_4286,c_39,c_45,c_46,c_47,c_1977]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_16,plain,
% 7.50/1.50      ( ~ v1_partfun1(X0,X1)
% 7.50/1.50      | ~ v4_relat_1(X0,X1)
% 7.50/1.50      | ~ v1_relat_1(X0)
% 7.50/1.50      | k1_relat_1(X0) = X1 ),
% 7.50/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_504,plain,
% 7.50/1.50      ( ~ v1_partfun1(X0_54,X1_54)
% 7.50/1.50      | ~ v4_relat_1(X0_54,X1_54)
% 7.50/1.50      | ~ v1_relat_1(X0_54)
% 7.50/1.50      | k1_relat_1(X0_54) = X1_54 ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1142,plain,
% 7.50/1.50      ( k1_relat_1(X0_54) = X1_54
% 7.50/1.50      | v1_partfun1(X0_54,X1_54) != iProver_top
% 7.50/1.50      | v4_relat_1(X0_54,X1_54) != iProver_top
% 7.50/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_5075,plain,
% 7.50/1.50      ( k1_relat_1(sK4) = sK2
% 7.50/1.50      | v4_relat_1(sK4,sK2) != iProver_top
% 7.50/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_5070,c_1142]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1835,plain,
% 7.50/1.50      ( ~ v1_partfun1(sK4,X0_54)
% 7.50/1.50      | ~ v4_relat_1(sK4,X0_54)
% 7.50/1.50      | ~ v1_relat_1(sK4)
% 7.50/1.50      | k1_relat_1(sK4) = X0_54 ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_504]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1847,plain,
% 7.50/1.50      ( ~ v1_partfun1(sK4,sK2)
% 7.50/1.50      | ~ v4_relat_1(sK4,sK2)
% 7.50/1.50      | ~ v1_relat_1(sK4)
% 7.50/1.50      | k1_relat_1(sK4) = sK2 ),
% 7.50/1.50      inference(instantiation,[status(thm)],[c_1835]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_5299,plain,
% 7.50/1.50      ( k1_relat_1(sK4) = sK2 ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_5075,c_36,c_30,c_29,c_28,c_1561,c_1593,c_1847,c_1976]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_8,plain,
% 7.50/1.50      ( ~ v1_relat_1(X0)
% 7.50/1.50      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 7.50/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_511,plain,
% 7.50/1.50      ( ~ v1_relat_1(X0_54)
% 7.50/1.50      | k1_relat_1(k7_relat_1(X0_54,X1_54)) = k3_xboole_0(k1_relat_1(X0_54),X1_54) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1135,plain,
% 7.50/1.50      ( k1_relat_1(k7_relat_1(X0_54,X1_54)) = k3_xboole_0(k1_relat_1(X0_54),X1_54)
% 7.50/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_2550,plain,
% 7.50/1.50      ( k1_relat_1(k7_relat_1(sK4,X0_54)) = k3_xboole_0(k1_relat_1(sK4),X0_54) ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_2360,c_1135]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_5302,plain,
% 7.50/1.50      ( k1_relat_1(k7_relat_1(sK4,X0_54)) = k3_xboole_0(sK2,X0_54) ),
% 7.50/1.50      inference(demodulation,[status(thm)],[c_5299,c_2550]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_11631,plain,
% 7.50/1.50      ( k3_xboole_0(sK2,sK3) = k1_relat_1(k1_xboole_0) ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_3872,c_5302]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_7,plain,
% 7.50/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.50/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_512,plain,
% 7.50/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_11648,plain,
% 7.50/1.50      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.50/1.50      inference(light_normalisation,[status(thm)],[c_11631,c_512]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13547,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.50/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.50/1.50      inference(light_normalisation,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_13546,c_7863,c_11648]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13548,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.50/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.50/1.50      inference(demodulation,[status(thm)],[c_13547,c_1981]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_7864,plain,
% 7.50/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_2360,c_6584]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13549,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.50/1.50      | k1_xboole_0 != k1_xboole_0
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.50/1.50      inference(light_normalisation,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_13548,c_7864,c_11648]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_13550,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.50/1.50      inference(equality_resolution_simp,[status(thm)],[c_13549]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_19,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_1(X3)
% 7.50/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X1)
% 7.50/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.50/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_283,plain,
% 7.50/1.50      ( ~ v1_funct_1(X3)
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X1)
% 7.50/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_19,c_23,c_22,c_21]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_284,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.50/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.50/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.50/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.50/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.50/1.50      | ~ v1_funct_1(X0)
% 7.50/1.50      | ~ v1_funct_1(X3)
% 7.50/1.50      | v1_xboole_0(X1)
% 7.50/1.50      | v1_xboole_0(X2)
% 7.50/1.50      | v1_xboole_0(X4)
% 7.50/1.50      | v1_xboole_0(X5)
% 7.50/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.50/1.50      inference(renaming,[status(thm)],[c_283]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_484,plain,
% 7.50/1.50      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.50/1.50      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.50/1.50      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.50/1.50      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.50/1.50      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.50/1.50      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.50/1.50      | ~ v1_funct_1(X0_54)
% 7.50/1.50      | ~ v1_funct_1(X3_54)
% 7.50/1.50      | v1_xboole_0(X1_54)
% 7.50/1.50      | v1_xboole_0(X2_54)
% 7.50/1.50      | v1_xboole_0(X4_54)
% 7.50/1.50      | v1_xboole_0(X5_54)
% 7.50/1.50      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_284]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_1161,plain,
% 7.50/1.50      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 7.50/1.50      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.50/1.50      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.50/1.50      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.50/1.50      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.50/1.50      | v1_funct_1(X2_54) != iProver_top
% 7.50/1.50      | v1_funct_1(X5_54) != iProver_top
% 7.50/1.50      | v1_xboole_0(X3_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X1_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X4_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_7394,plain,
% 7.50/1.50      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.50/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.50/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.50/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | v1_funct_1(X1_54) != iProver_top
% 7.50/1.50      | v1_funct_1(sK5) != iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X2_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_4706,c_1161]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_8309,plain,
% 7.50/1.50      ( v1_funct_1(X1_54) != iProver_top
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.50/1.50      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.50/1.50      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X2_54) = iProver_top ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_7394,c_39,c_42,c_48,c_49,c_50]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_8310,plain,
% 7.50/1.50      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.50/1.50      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.50/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.50/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.50/1.50      | v1_funct_1(X1_54) != iProver_top
% 7.50/1.50      | v1_xboole_0(X2_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.50/1.50      inference(renaming,[status(thm)],[c_8309]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_8325,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.50/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.50/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | v1_funct_1(sK4) != iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.50/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_4712,c_8310]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_9287,plain,
% 7.50/1.50      ( v1_xboole_0(X0_54) = iProver_top
% 7.50/1.50      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_8325,c_40,c_45,c_46,c_47]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_9288,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.50/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.50/1.50      inference(renaming,[status(thm)],[c_9287]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_9298,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.50/1.50      inference(superposition,[status(thm)],[c_1981,c_9288]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_9299,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.50/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.50/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.50/1.50      inference(demodulation,[status(thm)],[c_9298,c_1981]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_37,negated_conjecture,
% 7.50/1.50      ( ~ v1_xboole_0(sK0) ),
% 7.50/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_34,negated_conjecture,
% 7.50/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.50/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_9300,plain,
% 7.50/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.50/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.50/1.50      | v1_xboole_0(sK0)
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.50/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_9299]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_9397,plain,
% 7.50/1.50      ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
% 7.50/1.50      inference(global_propositional_subsumption,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_9299,c_37,c_34,c_32,c_9300]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_9398,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.50/1.50      inference(renaming,[status(thm)],[c_9397]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_11995,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.50/1.50      inference(demodulation,[status(thm)],[c_11648,c_9398]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_12006,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.50/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.50/1.50      inference(light_normalisation,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_11995,c_7863,c_7864]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_12007,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
% 7.50/1.50      inference(equality_resolution_simp,[status(thm)],[c_12006]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_24,negated_conjecture,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.50/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.50/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_498,negated_conjecture,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.50/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.50/1.50      inference(subtyping,[status(esa)],[c_24]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_2183,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.50/1.50      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.50/1.50      inference(demodulation,[status(thm)],[c_1981,c_498]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_4710,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.50/1.50      | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.50/1.50      inference(demodulation,[status(thm)],[c_4706,c_2183]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_4906,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.50/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.50/1.50      inference(demodulation,[status(thm)],[c_4710,c_4712]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_11996,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.50/1.50      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.50/1.50      inference(demodulation,[status(thm)],[c_11648,c_4906]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_12000,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.50/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.50/1.50      inference(light_normalisation,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_11996,c_7863,c_7864]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_12001,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.50/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.50/1.50      inference(equality_resolution_simp,[status(thm)],[c_12000]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_12009,plain,
% 7.50/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.50/1.50      inference(backward_subsumption_resolution,
% 7.50/1.50                [status(thm)],
% 7.50/1.50                [c_12007,c_12001]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_43,plain,
% 7.50/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_41,plain,
% 7.50/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(c_38,plain,
% 7.50/1.50      ( v1_xboole_0(sK0) != iProver_top ),
% 7.50/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.50/1.50  
% 7.50/1.50  cnf(contradiction,plain,
% 7.50/1.50      ( $false ),
% 7.50/1.50      inference(minisat,[status(thm)],[c_13550,c_12009,c_43,c_41,c_38]) ).
% 7.50/1.50  
% 7.50/1.50  
% 7.50/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.50/1.50  
% 7.50/1.50  ------                               Statistics
% 7.50/1.50  
% 7.50/1.50  ------ Selected
% 7.50/1.50  
% 7.50/1.50  total_time:                             0.54
% 7.50/1.50  
%------------------------------------------------------------------------------
