%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:31 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  190 (2152 expanded)
%              Number of clauses        :  119 ( 500 expanded)
%              Number of leaves         :   19 ( 871 expanded)
%              Depth                    :   25
%              Number of atoms          : 1144 (28274 expanded)
%              Number of equality atoms :  520 (6921 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f28,f38,f37,f36,f35,f34,f33])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f55,plain,(
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

fof(f56,plain,(
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

fof(f57,plain,(
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

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f53])).

fof(f71,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_988,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_996,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2232,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_996])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1345,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1508,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_2510,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2232,c_23,c_21,c_1508])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_991,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2231,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_996])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1340,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1503,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_2503,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2231,c_20,c_18,c_1503])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_222,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_408,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_409,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_411,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_28,c_26])).

cnf(c_428,plain,
    ( k4_xboole_0(X0,X1) = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_411])).

cnf(c_429,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_985,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_998,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2153,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k9_subset_1(sK0,X0,sK3) ),
    inference(superposition,[status(thm)],[c_985,c_998])).

cnf(c_2248,plain,
    ( k9_subset_1(sK0,sK2,sK3) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_429,c_2153])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_422,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) = X0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_222])).

cnf(c_423,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1023,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_0,c_423])).

cnf(c_2254,plain,
    ( k9_subset_1(sK0,sK2,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2248,c_1023])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_164,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_16,c_15,c_14])).

cnf(c_165,plain,
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
    inference(renaming,[status(thm)],[c_164])).

cnf(c_979,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_997,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1176,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_979,c_997])).

cnf(c_4496,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1
    | k2_partfun1(sK2,X0,X1,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,X0,X2,k1_xboole_0)
    | v1_funct_2(X2,sK3,X0) != iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_1176])).

cnf(c_4697,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1
    | k2_partfun1(sK3,X0,X2,k1_xboole_0) != k2_partfun1(sK2,X0,X1,k1_xboole_0)
    | v1_funct_2(X2,sK3,X0) != iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4496,c_2254])).

cnf(c_33,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12230,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1
    | k2_partfun1(sK3,X0,X2,k1_xboole_0) != k2_partfun1(sK2,X0,X1,k1_xboole_0)
    | v1_funct_2(X2,sK3,X0) != iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4697,c_33,c_34,c_35,c_36])).

cnf(c_12245,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
    | k2_partfun1(sK2,sK1,X0,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | v1_funct_2(X0,sK2,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_12230])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9,c_6])).

cnf(c_977,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_2035,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_991,c_977])).

cnf(c_12246,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
    | k2_partfun1(sK2,sK1,X0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0,sK2,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12245,c_2035])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_42,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12263,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
    | k2_partfun1(sK2,sK1,X0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0,sK2,sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12246,c_32,c_41,c_42,c_43])).

cnf(c_12264,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
    | k2_partfun1(sK2,sK1,X0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0,sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12263])).

cnf(c_12274,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2510,c_12264])).

cnf(c_2036,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_988,c_977])).

cnf(c_12275,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12274,c_2036])).

cnf(c_12276,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12275])).

cnf(c_994,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1121,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_994,c_997])).

cnf(c_3046,plain,
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
    inference(superposition,[status(thm)],[c_1121,c_996])).

cnf(c_992,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1069,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_992,c_997])).

cnf(c_5063,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_3046,c_1069])).

cnf(c_5068,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_5063])).

cnf(c_5303,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5068,c_32,c_35,c_41,c_42])).

cnf(c_5304,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_5303])).

cnf(c_5318,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_5304])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_39,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5671,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5318,c_33,c_38,c_39])).

cnf(c_5680,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_5671])).

cnf(c_5777,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5680,c_34])).

cnf(c_12277,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12276,c_5777])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_171,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_16,c_15,c_14])).

cnf(c_172,plain,
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
    inference(renaming,[status(thm)],[c_171])).

cnf(c_978,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_1148,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_978,c_997])).

cnf(c_3757,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2510,c_1148])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10941,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3757,c_32,c_33,c_38,c_39,c_40])).

cnf(c_10942,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10941])).

cnf(c_10961,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0,k1_xboole_0)
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_10942])).

cnf(c_11088,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
    | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10961,c_2036,c_2254])).

cnf(c_11560,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11088,c_34,c_35,c_36])).

cnf(c_11561,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
    | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11560])).

cnf(c_11571,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_11561])).

cnf(c_11572,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11571,c_2035])).

cnf(c_11573,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11572])).

cnf(c_11574,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11573,c_5777])).

cnf(c_17,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2319,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2254,c_17])).

cnf(c_2507,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2503,c_2319])).

cnf(c_2508,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2507,c_2035])).

cnf(c_2660,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2508,c_2036,c_2510])).

cnf(c_2661,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_2660])).

cnf(c_5781,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_5777,c_2661])).

cnf(c_5782,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_5781,c_5777])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12277,c_11574,c_5782,c_43,c_42,c_41,c_40,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:27:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.41/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/1.49  
% 6.41/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.41/1.49  
% 6.41/1.49  ------  iProver source info
% 6.41/1.49  
% 6.41/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.41/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.41/1.49  git: non_committed_changes: false
% 6.41/1.49  git: last_make_outside_of_git: false
% 6.41/1.49  
% 6.41/1.49  ------ 
% 6.41/1.49  
% 6.41/1.49  ------ Input Options
% 6.41/1.49  
% 6.41/1.49  --out_options                           all
% 6.41/1.49  --tptp_safe_out                         true
% 6.41/1.49  --problem_path                          ""
% 6.41/1.49  --include_path                          ""
% 6.41/1.49  --clausifier                            res/vclausify_rel
% 6.41/1.49  --clausifier_options                    --mode clausify
% 6.41/1.49  --stdin                                 false
% 6.41/1.49  --stats_out                             all
% 6.41/1.49  
% 6.41/1.49  ------ General Options
% 6.41/1.49  
% 6.41/1.49  --fof                                   false
% 6.41/1.49  --time_out_real                         305.
% 6.41/1.49  --time_out_virtual                      -1.
% 6.41/1.49  --symbol_type_check                     false
% 6.41/1.49  --clausify_out                          false
% 6.41/1.49  --sig_cnt_out                           false
% 6.41/1.49  --trig_cnt_out                          false
% 6.41/1.49  --trig_cnt_out_tolerance                1.
% 6.41/1.49  --trig_cnt_out_sk_spl                   false
% 6.41/1.49  --abstr_cl_out                          false
% 6.41/1.49  
% 6.41/1.49  ------ Global Options
% 6.41/1.49  
% 6.41/1.49  --schedule                              default
% 6.41/1.49  --add_important_lit                     false
% 6.41/1.49  --prop_solver_per_cl                    1000
% 6.41/1.49  --min_unsat_core                        false
% 6.41/1.49  --soft_assumptions                      false
% 6.41/1.49  --soft_lemma_size                       3
% 6.41/1.49  --prop_impl_unit_size                   0
% 6.41/1.49  --prop_impl_unit                        []
% 6.41/1.49  --share_sel_clauses                     true
% 6.41/1.49  --reset_solvers                         false
% 6.41/1.49  --bc_imp_inh                            [conj_cone]
% 6.41/1.49  --conj_cone_tolerance                   3.
% 6.41/1.49  --extra_neg_conj                        none
% 6.41/1.49  --large_theory_mode                     true
% 6.41/1.49  --prolific_symb_bound                   200
% 6.41/1.49  --lt_threshold                          2000
% 6.41/1.49  --clause_weak_htbl                      true
% 6.41/1.49  --gc_record_bc_elim                     false
% 6.41/1.49  
% 6.41/1.49  ------ Preprocessing Options
% 6.41/1.49  
% 6.41/1.49  --preprocessing_flag                    true
% 6.41/1.49  --time_out_prep_mult                    0.1
% 6.41/1.49  --splitting_mode                        input
% 6.41/1.49  --splitting_grd                         true
% 6.41/1.49  --splitting_cvd                         false
% 6.41/1.49  --splitting_cvd_svl                     false
% 6.41/1.49  --splitting_nvd                         32
% 6.41/1.49  --sub_typing                            true
% 6.41/1.49  --prep_gs_sim                           true
% 6.41/1.49  --prep_unflatten                        true
% 6.41/1.49  --prep_res_sim                          true
% 6.41/1.49  --prep_upred                            true
% 6.41/1.49  --prep_sem_filter                       exhaustive
% 6.41/1.49  --prep_sem_filter_out                   false
% 6.41/1.49  --pred_elim                             true
% 6.41/1.49  --res_sim_input                         true
% 6.41/1.49  --eq_ax_congr_red                       true
% 6.41/1.49  --pure_diseq_elim                       true
% 6.41/1.49  --brand_transform                       false
% 6.41/1.49  --non_eq_to_eq                          false
% 6.41/1.49  --prep_def_merge                        true
% 6.41/1.49  --prep_def_merge_prop_impl              false
% 6.41/1.49  --prep_def_merge_mbd                    true
% 6.41/1.49  --prep_def_merge_tr_red                 false
% 6.41/1.49  --prep_def_merge_tr_cl                  false
% 6.41/1.49  --smt_preprocessing                     true
% 6.41/1.49  --smt_ac_axioms                         fast
% 6.41/1.49  --preprocessed_out                      false
% 6.41/1.49  --preprocessed_stats                    false
% 6.41/1.49  
% 6.41/1.49  ------ Abstraction refinement Options
% 6.41/1.49  
% 6.41/1.49  --abstr_ref                             []
% 6.41/1.49  --abstr_ref_prep                        false
% 6.41/1.49  --abstr_ref_until_sat                   false
% 6.41/1.49  --abstr_ref_sig_restrict                funpre
% 6.41/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.41/1.49  --abstr_ref_under                       []
% 6.41/1.49  
% 6.41/1.49  ------ SAT Options
% 6.41/1.49  
% 6.41/1.49  --sat_mode                              false
% 6.41/1.49  --sat_fm_restart_options                ""
% 6.41/1.49  --sat_gr_def                            false
% 6.41/1.49  --sat_epr_types                         true
% 6.41/1.49  --sat_non_cyclic_types                  false
% 6.41/1.49  --sat_finite_models                     false
% 6.41/1.49  --sat_fm_lemmas                         false
% 6.41/1.49  --sat_fm_prep                           false
% 6.41/1.49  --sat_fm_uc_incr                        true
% 6.41/1.49  --sat_out_model                         small
% 6.41/1.49  --sat_out_clauses                       false
% 6.41/1.49  
% 6.41/1.49  ------ QBF Options
% 6.41/1.49  
% 6.41/1.49  --qbf_mode                              false
% 6.41/1.49  --qbf_elim_univ                         false
% 6.41/1.49  --qbf_dom_inst                          none
% 6.41/1.49  --qbf_dom_pre_inst                      false
% 6.41/1.49  --qbf_sk_in                             false
% 6.41/1.49  --qbf_pred_elim                         true
% 6.41/1.49  --qbf_split                             512
% 6.41/1.49  
% 6.41/1.49  ------ BMC1 Options
% 6.41/1.49  
% 6.41/1.49  --bmc1_incremental                      false
% 6.41/1.49  --bmc1_axioms                           reachable_all
% 6.41/1.49  --bmc1_min_bound                        0
% 6.41/1.49  --bmc1_max_bound                        -1
% 6.41/1.49  --bmc1_max_bound_default                -1
% 6.41/1.49  --bmc1_symbol_reachability              true
% 6.41/1.49  --bmc1_property_lemmas                  false
% 6.41/1.49  --bmc1_k_induction                      false
% 6.41/1.49  --bmc1_non_equiv_states                 false
% 6.41/1.49  --bmc1_deadlock                         false
% 6.41/1.49  --bmc1_ucm                              false
% 6.41/1.49  --bmc1_add_unsat_core                   none
% 6.41/1.49  --bmc1_unsat_core_children              false
% 6.41/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.41/1.49  --bmc1_out_stat                         full
% 6.41/1.49  --bmc1_ground_init                      false
% 6.41/1.49  --bmc1_pre_inst_next_state              false
% 6.41/1.49  --bmc1_pre_inst_state                   false
% 6.41/1.49  --bmc1_pre_inst_reach_state             false
% 6.41/1.49  --bmc1_out_unsat_core                   false
% 6.41/1.49  --bmc1_aig_witness_out                  false
% 6.41/1.49  --bmc1_verbose                          false
% 6.41/1.49  --bmc1_dump_clauses_tptp                false
% 6.41/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.41/1.49  --bmc1_dump_file                        -
% 6.41/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.41/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.41/1.49  --bmc1_ucm_extend_mode                  1
% 6.41/1.49  --bmc1_ucm_init_mode                    2
% 6.41/1.49  --bmc1_ucm_cone_mode                    none
% 6.41/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.41/1.49  --bmc1_ucm_relax_model                  4
% 6.41/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.41/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.41/1.49  --bmc1_ucm_layered_model                none
% 6.41/1.49  --bmc1_ucm_max_lemma_size               10
% 6.41/1.49  
% 6.41/1.49  ------ AIG Options
% 6.41/1.49  
% 6.41/1.49  --aig_mode                              false
% 6.41/1.49  
% 6.41/1.49  ------ Instantiation Options
% 6.41/1.49  
% 6.41/1.49  --instantiation_flag                    true
% 6.41/1.49  --inst_sos_flag                         false
% 6.41/1.49  --inst_sos_phase                        true
% 6.41/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.41/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.41/1.49  --inst_lit_sel_side                     num_symb
% 6.41/1.49  --inst_solver_per_active                1400
% 6.41/1.49  --inst_solver_calls_frac                1.
% 6.41/1.49  --inst_passive_queue_type               priority_queues
% 6.41/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.41/1.49  --inst_passive_queues_freq              [25;2]
% 6.41/1.49  --inst_dismatching                      true
% 6.41/1.49  --inst_eager_unprocessed_to_passive     true
% 6.41/1.49  --inst_prop_sim_given                   true
% 6.41/1.49  --inst_prop_sim_new                     false
% 6.41/1.49  --inst_subs_new                         false
% 6.41/1.49  --inst_eq_res_simp                      false
% 6.41/1.49  --inst_subs_given                       false
% 6.41/1.49  --inst_orphan_elimination               true
% 6.41/1.49  --inst_learning_loop_flag               true
% 6.41/1.49  --inst_learning_start                   3000
% 6.41/1.49  --inst_learning_factor                  2
% 6.41/1.49  --inst_start_prop_sim_after_learn       3
% 6.41/1.49  --inst_sel_renew                        solver
% 6.41/1.49  --inst_lit_activity_flag                true
% 6.41/1.49  --inst_restr_to_given                   false
% 6.41/1.49  --inst_activity_threshold               500
% 6.41/1.49  --inst_out_proof                        true
% 6.41/1.49  
% 6.41/1.49  ------ Resolution Options
% 6.41/1.49  
% 6.41/1.49  --resolution_flag                       true
% 6.41/1.49  --res_lit_sel                           adaptive
% 6.41/1.49  --res_lit_sel_side                      none
% 6.41/1.49  --res_ordering                          kbo
% 6.41/1.49  --res_to_prop_solver                    active
% 6.41/1.49  --res_prop_simpl_new                    false
% 6.41/1.49  --res_prop_simpl_given                  true
% 6.41/1.49  --res_passive_queue_type                priority_queues
% 6.41/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.41/1.49  --res_passive_queues_freq               [15;5]
% 6.41/1.49  --res_forward_subs                      full
% 6.41/1.49  --res_backward_subs                     full
% 6.41/1.49  --res_forward_subs_resolution           true
% 6.41/1.49  --res_backward_subs_resolution          true
% 6.41/1.49  --res_orphan_elimination                true
% 6.41/1.49  --res_time_limit                        2.
% 6.41/1.49  --res_out_proof                         true
% 6.41/1.49  
% 6.41/1.49  ------ Superposition Options
% 6.41/1.49  
% 6.41/1.49  --superposition_flag                    true
% 6.41/1.49  --sup_passive_queue_type                priority_queues
% 6.41/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.41/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.41/1.49  --demod_completeness_check              fast
% 6.41/1.49  --demod_use_ground                      true
% 6.41/1.49  --sup_to_prop_solver                    passive
% 6.41/1.49  --sup_prop_simpl_new                    true
% 6.41/1.49  --sup_prop_simpl_given                  true
% 6.41/1.49  --sup_fun_splitting                     false
% 6.41/1.49  --sup_smt_interval                      50000
% 6.41/1.49  
% 6.41/1.49  ------ Superposition Simplification Setup
% 6.41/1.49  
% 6.41/1.49  --sup_indices_passive                   []
% 6.41/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.41/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.49  --sup_full_bw                           [BwDemod]
% 6.41/1.49  --sup_immed_triv                        [TrivRules]
% 6.41/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.41/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.49  --sup_immed_bw_main                     []
% 6.41/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.41/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.49  
% 6.41/1.49  ------ Combination Options
% 6.41/1.49  
% 6.41/1.49  --comb_res_mult                         3
% 6.41/1.49  --comb_sup_mult                         2
% 6.41/1.49  --comb_inst_mult                        10
% 6.41/1.49  
% 6.41/1.49  ------ Debug Options
% 6.41/1.49  
% 6.41/1.49  --dbg_backtrace                         false
% 6.41/1.49  --dbg_dump_prop_clauses                 false
% 6.41/1.49  --dbg_dump_prop_clauses_file            -
% 6.41/1.49  --dbg_out_stat                          false
% 6.41/1.49  ------ Parsing...
% 6.41/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.41/1.49  
% 6.41/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.41/1.49  
% 6.41/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.41/1.49  
% 6.41/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.41/1.49  ------ Proving...
% 6.41/1.49  ------ Problem Properties 
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  clauses                                 26
% 6.41/1.49  conjectures                             13
% 6.41/1.49  EPR                                     8
% 6.41/1.49  Horn                                    20
% 6.41/1.49  unary                                   15
% 6.41/1.49  binary                                  2
% 6.41/1.49  lits                                    112
% 6.41/1.49  lits eq                                 15
% 6.41/1.49  fd_pure                                 0
% 6.41/1.49  fd_pseudo                               0
% 6.41/1.49  fd_cond                                 0
% 6.41/1.49  fd_pseudo_cond                          0
% 6.41/1.49  AC symbols                              0
% 6.41/1.49  
% 6.41/1.49  ------ Schedule dynamic 5 is on 
% 6.41/1.49  
% 6.41/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  ------ 
% 6.41/1.49  Current options:
% 6.41/1.49  ------ 
% 6.41/1.49  
% 6.41/1.49  ------ Input Options
% 6.41/1.49  
% 6.41/1.49  --out_options                           all
% 6.41/1.49  --tptp_safe_out                         true
% 6.41/1.49  --problem_path                          ""
% 6.41/1.49  --include_path                          ""
% 6.41/1.49  --clausifier                            res/vclausify_rel
% 6.41/1.49  --clausifier_options                    --mode clausify
% 6.41/1.49  --stdin                                 false
% 6.41/1.49  --stats_out                             all
% 6.41/1.49  
% 6.41/1.49  ------ General Options
% 6.41/1.49  
% 6.41/1.49  --fof                                   false
% 6.41/1.49  --time_out_real                         305.
% 6.41/1.49  --time_out_virtual                      -1.
% 6.41/1.49  --symbol_type_check                     false
% 6.41/1.49  --clausify_out                          false
% 6.41/1.49  --sig_cnt_out                           false
% 6.41/1.49  --trig_cnt_out                          false
% 6.41/1.49  --trig_cnt_out_tolerance                1.
% 6.41/1.49  --trig_cnt_out_sk_spl                   false
% 6.41/1.49  --abstr_cl_out                          false
% 6.41/1.49  
% 6.41/1.49  ------ Global Options
% 6.41/1.49  
% 6.41/1.49  --schedule                              default
% 6.41/1.49  --add_important_lit                     false
% 6.41/1.49  --prop_solver_per_cl                    1000
% 6.41/1.49  --min_unsat_core                        false
% 6.41/1.49  --soft_assumptions                      false
% 6.41/1.49  --soft_lemma_size                       3
% 6.41/1.49  --prop_impl_unit_size                   0
% 6.41/1.49  --prop_impl_unit                        []
% 6.41/1.49  --share_sel_clauses                     true
% 6.41/1.49  --reset_solvers                         false
% 6.41/1.49  --bc_imp_inh                            [conj_cone]
% 6.41/1.49  --conj_cone_tolerance                   3.
% 6.41/1.49  --extra_neg_conj                        none
% 6.41/1.49  --large_theory_mode                     true
% 6.41/1.49  --prolific_symb_bound                   200
% 6.41/1.49  --lt_threshold                          2000
% 6.41/1.49  --clause_weak_htbl                      true
% 6.41/1.49  --gc_record_bc_elim                     false
% 6.41/1.49  
% 6.41/1.49  ------ Preprocessing Options
% 6.41/1.49  
% 6.41/1.49  --preprocessing_flag                    true
% 6.41/1.49  --time_out_prep_mult                    0.1
% 6.41/1.49  --splitting_mode                        input
% 6.41/1.49  --splitting_grd                         true
% 6.41/1.49  --splitting_cvd                         false
% 6.41/1.49  --splitting_cvd_svl                     false
% 6.41/1.49  --splitting_nvd                         32
% 6.41/1.49  --sub_typing                            true
% 6.41/1.49  --prep_gs_sim                           true
% 6.41/1.49  --prep_unflatten                        true
% 6.41/1.49  --prep_res_sim                          true
% 6.41/1.49  --prep_upred                            true
% 6.41/1.49  --prep_sem_filter                       exhaustive
% 6.41/1.49  --prep_sem_filter_out                   false
% 6.41/1.49  --pred_elim                             true
% 6.41/1.49  --res_sim_input                         true
% 6.41/1.49  --eq_ax_congr_red                       true
% 6.41/1.49  --pure_diseq_elim                       true
% 6.41/1.49  --brand_transform                       false
% 6.41/1.49  --non_eq_to_eq                          false
% 6.41/1.49  --prep_def_merge                        true
% 6.41/1.49  --prep_def_merge_prop_impl              false
% 6.41/1.49  --prep_def_merge_mbd                    true
% 6.41/1.49  --prep_def_merge_tr_red                 false
% 6.41/1.49  --prep_def_merge_tr_cl                  false
% 6.41/1.49  --smt_preprocessing                     true
% 6.41/1.49  --smt_ac_axioms                         fast
% 6.41/1.49  --preprocessed_out                      false
% 6.41/1.49  --preprocessed_stats                    false
% 6.41/1.49  
% 6.41/1.49  ------ Abstraction refinement Options
% 6.41/1.49  
% 6.41/1.49  --abstr_ref                             []
% 6.41/1.49  --abstr_ref_prep                        false
% 6.41/1.49  --abstr_ref_until_sat                   false
% 6.41/1.49  --abstr_ref_sig_restrict                funpre
% 6.41/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.41/1.49  --abstr_ref_under                       []
% 6.41/1.49  
% 6.41/1.49  ------ SAT Options
% 6.41/1.49  
% 6.41/1.49  --sat_mode                              false
% 6.41/1.49  --sat_fm_restart_options                ""
% 6.41/1.49  --sat_gr_def                            false
% 6.41/1.49  --sat_epr_types                         true
% 6.41/1.49  --sat_non_cyclic_types                  false
% 6.41/1.49  --sat_finite_models                     false
% 6.41/1.49  --sat_fm_lemmas                         false
% 6.41/1.49  --sat_fm_prep                           false
% 6.41/1.49  --sat_fm_uc_incr                        true
% 6.41/1.49  --sat_out_model                         small
% 6.41/1.49  --sat_out_clauses                       false
% 6.41/1.49  
% 6.41/1.49  ------ QBF Options
% 6.41/1.49  
% 6.41/1.49  --qbf_mode                              false
% 6.41/1.49  --qbf_elim_univ                         false
% 6.41/1.49  --qbf_dom_inst                          none
% 6.41/1.49  --qbf_dom_pre_inst                      false
% 6.41/1.49  --qbf_sk_in                             false
% 6.41/1.49  --qbf_pred_elim                         true
% 6.41/1.49  --qbf_split                             512
% 6.41/1.49  
% 6.41/1.49  ------ BMC1 Options
% 6.41/1.49  
% 6.41/1.49  --bmc1_incremental                      false
% 6.41/1.49  --bmc1_axioms                           reachable_all
% 6.41/1.49  --bmc1_min_bound                        0
% 6.41/1.49  --bmc1_max_bound                        -1
% 6.41/1.49  --bmc1_max_bound_default                -1
% 6.41/1.49  --bmc1_symbol_reachability              true
% 6.41/1.49  --bmc1_property_lemmas                  false
% 6.41/1.49  --bmc1_k_induction                      false
% 6.41/1.49  --bmc1_non_equiv_states                 false
% 6.41/1.49  --bmc1_deadlock                         false
% 6.41/1.49  --bmc1_ucm                              false
% 6.41/1.49  --bmc1_add_unsat_core                   none
% 6.41/1.49  --bmc1_unsat_core_children              false
% 6.41/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.41/1.49  --bmc1_out_stat                         full
% 6.41/1.49  --bmc1_ground_init                      false
% 6.41/1.49  --bmc1_pre_inst_next_state              false
% 6.41/1.49  --bmc1_pre_inst_state                   false
% 6.41/1.49  --bmc1_pre_inst_reach_state             false
% 6.41/1.49  --bmc1_out_unsat_core                   false
% 6.41/1.49  --bmc1_aig_witness_out                  false
% 6.41/1.49  --bmc1_verbose                          false
% 6.41/1.49  --bmc1_dump_clauses_tptp                false
% 6.41/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.41/1.49  --bmc1_dump_file                        -
% 6.41/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.41/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.41/1.49  --bmc1_ucm_extend_mode                  1
% 6.41/1.49  --bmc1_ucm_init_mode                    2
% 6.41/1.49  --bmc1_ucm_cone_mode                    none
% 6.41/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.41/1.49  --bmc1_ucm_relax_model                  4
% 6.41/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.41/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.41/1.49  --bmc1_ucm_layered_model                none
% 6.41/1.49  --bmc1_ucm_max_lemma_size               10
% 6.41/1.49  
% 6.41/1.49  ------ AIG Options
% 6.41/1.49  
% 6.41/1.49  --aig_mode                              false
% 6.41/1.49  
% 6.41/1.49  ------ Instantiation Options
% 6.41/1.49  
% 6.41/1.49  --instantiation_flag                    true
% 6.41/1.49  --inst_sos_flag                         false
% 6.41/1.49  --inst_sos_phase                        true
% 6.41/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.41/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.41/1.49  --inst_lit_sel_side                     none
% 6.41/1.49  --inst_solver_per_active                1400
% 6.41/1.49  --inst_solver_calls_frac                1.
% 6.41/1.49  --inst_passive_queue_type               priority_queues
% 6.41/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.41/1.49  --inst_passive_queues_freq              [25;2]
% 6.41/1.49  --inst_dismatching                      true
% 6.41/1.49  --inst_eager_unprocessed_to_passive     true
% 6.41/1.49  --inst_prop_sim_given                   true
% 6.41/1.49  --inst_prop_sim_new                     false
% 6.41/1.49  --inst_subs_new                         false
% 6.41/1.49  --inst_eq_res_simp                      false
% 6.41/1.49  --inst_subs_given                       false
% 6.41/1.49  --inst_orphan_elimination               true
% 6.41/1.49  --inst_learning_loop_flag               true
% 6.41/1.49  --inst_learning_start                   3000
% 6.41/1.49  --inst_learning_factor                  2
% 6.41/1.49  --inst_start_prop_sim_after_learn       3
% 6.41/1.49  --inst_sel_renew                        solver
% 6.41/1.49  --inst_lit_activity_flag                true
% 6.41/1.49  --inst_restr_to_given                   false
% 6.41/1.49  --inst_activity_threshold               500
% 6.41/1.49  --inst_out_proof                        true
% 6.41/1.49  
% 6.41/1.49  ------ Resolution Options
% 6.41/1.49  
% 6.41/1.49  --resolution_flag                       false
% 6.41/1.49  --res_lit_sel                           adaptive
% 6.41/1.49  --res_lit_sel_side                      none
% 6.41/1.49  --res_ordering                          kbo
% 6.41/1.49  --res_to_prop_solver                    active
% 6.41/1.49  --res_prop_simpl_new                    false
% 6.41/1.49  --res_prop_simpl_given                  true
% 6.41/1.49  --res_passive_queue_type                priority_queues
% 6.41/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.41/1.49  --res_passive_queues_freq               [15;5]
% 6.41/1.49  --res_forward_subs                      full
% 6.41/1.49  --res_backward_subs                     full
% 6.41/1.49  --res_forward_subs_resolution           true
% 6.41/1.49  --res_backward_subs_resolution          true
% 6.41/1.49  --res_orphan_elimination                true
% 6.41/1.49  --res_time_limit                        2.
% 6.41/1.49  --res_out_proof                         true
% 6.41/1.49  
% 6.41/1.49  ------ Superposition Options
% 6.41/1.49  
% 6.41/1.49  --superposition_flag                    true
% 6.41/1.49  --sup_passive_queue_type                priority_queues
% 6.41/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.41/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.41/1.49  --demod_completeness_check              fast
% 6.41/1.49  --demod_use_ground                      true
% 6.41/1.49  --sup_to_prop_solver                    passive
% 6.41/1.49  --sup_prop_simpl_new                    true
% 6.41/1.49  --sup_prop_simpl_given                  true
% 6.41/1.49  --sup_fun_splitting                     false
% 6.41/1.49  --sup_smt_interval                      50000
% 6.41/1.49  
% 6.41/1.49  ------ Superposition Simplification Setup
% 6.41/1.49  
% 6.41/1.49  --sup_indices_passive                   []
% 6.41/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.41/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.49  --sup_full_bw                           [BwDemod]
% 6.41/1.49  --sup_immed_triv                        [TrivRules]
% 6.41/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.41/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.49  --sup_immed_bw_main                     []
% 6.41/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.41/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.49  
% 6.41/1.49  ------ Combination Options
% 6.41/1.49  
% 6.41/1.49  --comb_res_mult                         3
% 6.41/1.49  --comb_sup_mult                         2
% 6.41/1.49  --comb_inst_mult                        10
% 6.41/1.49  
% 6.41/1.49  ------ Debug Options
% 6.41/1.49  
% 6.41/1.49  --dbg_backtrace                         false
% 6.41/1.49  --dbg_dump_prop_clauses                 false
% 6.41/1.49  --dbg_dump_prop_clauses_file            -
% 6.41/1.49  --dbg_out_stat                          false
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  ------ Proving...
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  % SZS status Theorem for theBenchmark.p
% 6.41/1.49  
% 6.41/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.41/1.49  
% 6.41/1.49  fof(f13,conjecture,(
% 6.41/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f14,negated_conjecture,(
% 6.41/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.41/1.49    inference(negated_conjecture,[],[f13])).
% 6.41/1.49  
% 6.41/1.49  fof(f27,plain,(
% 6.41/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.41/1.49    inference(ennf_transformation,[],[f14])).
% 6.41/1.49  
% 6.41/1.49  fof(f28,plain,(
% 6.41/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.41/1.49    inference(flattening,[],[f27])).
% 6.41/1.49  
% 6.41/1.49  fof(f38,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 6.41/1.49    introduced(choice_axiom,[])).
% 6.41/1.49  
% 6.41/1.49  fof(f37,plain,(
% 6.41/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 6.41/1.49    introduced(choice_axiom,[])).
% 6.41/1.49  
% 6.41/1.49  fof(f36,plain,(
% 6.41/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 6.41/1.49    introduced(choice_axiom,[])).
% 6.41/1.49  
% 6.41/1.49  fof(f35,plain,(
% 6.41/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 6.41/1.49    introduced(choice_axiom,[])).
% 6.41/1.49  
% 6.41/1.49  fof(f34,plain,(
% 6.41/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 6.41/1.49    introduced(choice_axiom,[])).
% 6.41/1.49  
% 6.41/1.49  fof(f33,plain,(
% 6.41/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 6.41/1.49    introduced(choice_axiom,[])).
% 6.41/1.49  
% 6.41/1.49  fof(f39,plain,(
% 6.41/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 6.41/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f28,f38,f37,f36,f35,f34,f33])).
% 6.41/1.49  
% 6.41/1.49  fof(f67,plain,(
% 6.41/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f10,axiom,(
% 6.41/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f21,plain,(
% 6.41/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.41/1.49    inference(ennf_transformation,[],[f10])).
% 6.41/1.49  
% 6.41/1.49  fof(f22,plain,(
% 6.41/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.41/1.49    inference(flattening,[],[f21])).
% 6.41/1.49  
% 6.41/1.49  fof(f51,plain,(
% 6.41/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f22])).
% 6.41/1.49  
% 6.41/1.49  fof(f65,plain,(
% 6.41/1.49    v1_funct_1(sK4)),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f70,plain,(
% 6.41/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f68,plain,(
% 6.41/1.49    v1_funct_1(sK5)),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f4,axiom,(
% 6.41/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f29,plain,(
% 6.41/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 6.41/1.49    inference(nnf_transformation,[],[f4])).
% 6.41/1.49  
% 6.41/1.49  fof(f43,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f29])).
% 6.41/1.49  
% 6.41/1.49  fof(f8,axiom,(
% 6.41/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f18,plain,(
% 6.41/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.41/1.49    inference(ennf_transformation,[],[f8])).
% 6.41/1.49  
% 6.41/1.49  fof(f19,plain,(
% 6.41/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.41/1.49    inference(flattening,[],[f18])).
% 6.41/1.49  
% 6.41/1.49  fof(f30,plain,(
% 6.41/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.41/1.49    inference(nnf_transformation,[],[f19])).
% 6.41/1.49  
% 6.41/1.49  fof(f48,plain,(
% 6.41/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f30])).
% 6.41/1.49  
% 6.41/1.49  fof(f64,plain,(
% 6.41/1.49    r1_subset_1(sK2,sK3)),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f60,plain,(
% 6.41/1.49    ~v1_xboole_0(sK2)),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f62,plain,(
% 6.41/1.49    ~v1_xboole_0(sK3)),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f63,plain,(
% 6.41/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f5,axiom,(
% 6.41/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f15,plain,(
% 6.41/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.41/1.49    inference(ennf_transformation,[],[f5])).
% 6.41/1.49  
% 6.41/1.49  fof(f45,plain,(
% 6.41/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f15])).
% 6.41/1.49  
% 6.41/1.49  fof(f2,axiom,(
% 6.41/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f41,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f2])).
% 6.41/1.49  
% 6.41/1.49  fof(f73,plain,(
% 6.41/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(definition_unfolding,[],[f45,f41])).
% 6.41/1.49  
% 6.41/1.49  fof(f1,axiom,(
% 6.41/1.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f40,plain,(
% 6.41/1.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f1])).
% 6.41/1.49  
% 6.41/1.49  fof(f72,plain,(
% 6.41/1.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 6.41/1.49    inference(definition_unfolding,[],[f40,f41])).
% 6.41/1.49  
% 6.41/1.49  fof(f3,axiom,(
% 6.41/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f42,plain,(
% 6.41/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f3])).
% 6.41/1.49  
% 6.41/1.49  fof(f11,axiom,(
% 6.41/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f23,plain,(
% 6.41/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.41/1.49    inference(ennf_transformation,[],[f11])).
% 6.41/1.49  
% 6.41/1.49  fof(f24,plain,(
% 6.41/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.41/1.49    inference(flattening,[],[f23])).
% 6.41/1.49  
% 6.41/1.49  fof(f31,plain,(
% 6.41/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.41/1.49    inference(nnf_transformation,[],[f24])).
% 6.41/1.49  
% 6.41/1.49  fof(f32,plain,(
% 6.41/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.41/1.49    inference(flattening,[],[f31])).
% 6.41/1.49  
% 6.41/1.49  fof(f52,plain,(
% 6.41/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f32])).
% 6.41/1.49  
% 6.41/1.49  fof(f77,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(equality_resolution,[],[f52])).
% 6.41/1.49  
% 6.41/1.49  fof(f12,axiom,(
% 6.41/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f25,plain,(
% 6.41/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.41/1.49    inference(ennf_transformation,[],[f12])).
% 6.41/1.49  
% 6.41/1.49  fof(f26,plain,(
% 6.41/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.41/1.49    inference(flattening,[],[f25])).
% 6.41/1.49  
% 6.41/1.49  fof(f55,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f26])).
% 6.41/1.49  
% 6.41/1.49  fof(f56,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f26])).
% 6.41/1.49  
% 6.41/1.49  fof(f57,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f26])).
% 6.41/1.49  
% 6.41/1.49  fof(f6,axiom,(
% 6.41/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f16,plain,(
% 6.41/1.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 6.41/1.49    inference(ennf_transformation,[],[f6])).
% 6.41/1.49  
% 6.41/1.49  fof(f46,plain,(
% 6.41/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f16])).
% 6.41/1.49  
% 6.41/1.49  fof(f61,plain,(
% 6.41/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f9,axiom,(
% 6.41/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f20,plain,(
% 6.41/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.49    inference(ennf_transformation,[],[f9])).
% 6.41/1.49  
% 6.41/1.49  fof(f50,plain,(
% 6.41/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f20])).
% 6.41/1.49  
% 6.41/1.49  fof(f7,axiom,(
% 6.41/1.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 6.41/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f17,plain,(
% 6.41/1.49    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 6.41/1.49    inference(ennf_transformation,[],[f7])).
% 6.41/1.49  
% 6.41/1.49  fof(f47,plain,(
% 6.41/1.49    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f17])).
% 6.41/1.49  
% 6.41/1.49  fof(f59,plain,(
% 6.41/1.49    ~v1_xboole_0(sK1)),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f69,plain,(
% 6.41/1.49    v1_funct_2(sK5,sK3,sK1)),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f66,plain,(
% 6.41/1.49    v1_funct_2(sK4,sK2,sK1)),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  fof(f53,plain,(
% 6.41/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f32])).
% 6.41/1.49  
% 6.41/1.49  fof(f76,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(equality_resolution,[],[f53])).
% 6.41/1.49  
% 6.41/1.49  fof(f71,plain,(
% 6.41/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 6.41/1.49    inference(cnf_transformation,[],[f39])).
% 6.41/1.49  
% 6.41/1.49  cnf(c_21,negated_conjecture,
% 6.41/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.41/1.49      inference(cnf_transformation,[],[f67]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_988,plain,
% 6.41/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_10,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.41/1.49      inference(cnf_transformation,[],[f51]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_996,plain,
% 6.41/1.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2232,plain,
% 6.41/1.49      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 6.41/1.49      | v1_funct_1(sK4) != iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_988,c_996]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_23,negated_conjecture,
% 6.41/1.49      ( v1_funct_1(sK4) ),
% 6.41/1.49      inference(cnf_transformation,[],[f65]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1345,plain,
% 6.41/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.41/1.49      | ~ v1_funct_1(sK4)
% 6.41/1.49      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1508,plain,
% 6.41/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.41/1.49      | ~ v1_funct_1(sK4)
% 6.41/1.49      | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1345]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2510,plain,
% 6.41/1.49      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_2232,c_23,c_21,c_1508]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_18,negated_conjecture,
% 6.41/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.41/1.49      inference(cnf_transformation,[],[f70]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_991,plain,
% 6.41/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2231,plain,
% 6.41/1.49      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 6.41/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_991,c_996]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_20,negated_conjecture,
% 6.41/1.49      ( v1_funct_1(sK5) ),
% 6.41/1.49      inference(cnf_transformation,[],[f68]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1340,plain,
% 6.41/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.41/1.49      | ~ v1_funct_1(sK5)
% 6.41/1.49      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1503,plain,
% 6.41/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 6.41/1.49      | ~ v1_funct_1(sK5)
% 6.41/1.49      | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1340]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2503,plain,
% 6.41/1.49      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_2231,c_20,c_18,c_1503]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_3,plain,
% 6.41/1.49      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 6.41/1.49      inference(cnf_transformation,[],[f43]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_222,plain,
% 6.41/1.49      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 6.41/1.49      inference(prop_impl,[status(thm)],[c_3]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_8,plain,
% 6.41/1.49      ( ~ r1_subset_1(X0,X1)
% 6.41/1.49      | r1_xboole_0(X0,X1)
% 6.41/1.49      | v1_xboole_0(X0)
% 6.41/1.49      | v1_xboole_0(X1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f48]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_24,negated_conjecture,
% 6.41/1.49      ( r1_subset_1(sK2,sK3) ),
% 6.41/1.49      inference(cnf_transformation,[],[f64]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_408,plain,
% 6.41/1.49      ( r1_xboole_0(X0,X1)
% 6.41/1.49      | v1_xboole_0(X0)
% 6.41/1.49      | v1_xboole_0(X1)
% 6.41/1.49      | sK3 != X1
% 6.41/1.49      | sK2 != X0 ),
% 6.41/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_409,plain,
% 6.41/1.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 6.41/1.49      inference(unflattening,[status(thm)],[c_408]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_28,negated_conjecture,
% 6.41/1.49      ( ~ v1_xboole_0(sK2) ),
% 6.41/1.49      inference(cnf_transformation,[],[f60]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_26,negated_conjecture,
% 6.41/1.49      ( ~ v1_xboole_0(sK3) ),
% 6.41/1.49      inference(cnf_transformation,[],[f62]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_411,plain,
% 6.41/1.49      ( r1_xboole_0(sK2,sK3) ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_409,c_28,c_26]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_428,plain,
% 6.41/1.49      ( k4_xboole_0(X0,X1) = X0 | sK3 != X1 | sK2 != X0 ),
% 6.41/1.49      inference(resolution_lifted,[status(thm)],[c_222,c_411]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_429,plain,
% 6.41/1.49      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 6.41/1.49      inference(unflattening,[status(thm)],[c_428]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_25,negated_conjecture,
% 6.41/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.41/1.49      inference(cnf_transformation,[],[f63]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_985,plain,
% 6.41/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_4,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.41/1.49      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 6.41/1.49      inference(cnf_transformation,[],[f73]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_998,plain,
% 6.41/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2153,plain,
% 6.41/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k9_subset_1(sK0,X0,sK3) ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_985,c_998]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2248,plain,
% 6.41/1.49      ( k9_subset_1(sK0,sK2,sK3) = k4_xboole_0(sK2,sK2) ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_429,c_2153]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_0,plain,
% 6.41/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 6.41/1.49      inference(cnf_transformation,[],[f72]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1,plain,
% 6.41/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 6.41/1.49      inference(cnf_transformation,[],[f42]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_422,plain,
% 6.41/1.49      ( X0 != X1 | k4_xboole_0(X0,X2) = X0 | k1_xboole_0 != X2 ),
% 6.41/1.49      inference(resolution_lifted,[status(thm)],[c_1,c_222]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_423,plain,
% 6.41/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.41/1.49      inference(unflattening,[status(thm)],[c_422]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1023,plain,
% 6.41/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.41/1.49      inference(light_normalisation,[status(thm)],[c_0,c_423]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2254,plain,
% 6.41/1.49      ( k9_subset_1(sK0,sK2,sK3) = k1_xboole_0 ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_2248,c_1023]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_13,plain,
% 6.41/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_1(X3)
% 6.41/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X1)
% 6.41/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.41/1.49      inference(cnf_transformation,[],[f77]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_16,plain,
% 6.41/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_1(X3)
% 6.41/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f55]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_15,plain,
% 6.41/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_1(X3)
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f56]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_14,plain,
% 6.41/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_1(X3)
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f57]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_164,plain,
% 6.41/1.49      ( ~ v1_funct_1(X3)
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X1)
% 6.41/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_13,c_16,c_15,c_14]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_165,plain,
% 6.41/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_1(X3)
% 6.41/1.49      | v1_xboole_0(X1)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.41/1.49      inference(renaming,[status(thm)],[c_164]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_979,plain,
% 6.41/1.49      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 6.41/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.41/1.49      | v1_funct_2(X5,X4,X1) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_funct_1(X5) != iProver_top
% 6.41/1.49      | v1_xboole_0(X3) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top
% 6.41/1.49      | v1_xboole_0(X4) = iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.41/1.49      | ~ v1_xboole_0(X1)
% 6.41/1.49      | v1_xboole_0(X0) ),
% 6.41/1.49      inference(cnf_transformation,[],[f46]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_997,plain,
% 6.41/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.41/1.49      | v1_xboole_0(X1) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1176,plain,
% 6.41/1.49      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
% 6.41/1.49      | v1_funct_2(X5,X4,X1) != iProver_top
% 6.41/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 6.41/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X5) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top
% 6.41/1.49      | v1_xboole_0(X4) = iProver_top ),
% 6.41/1.49      inference(forward_subsumption_resolution,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_979,c_997]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_4496,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1
% 6.41/1.49      | k2_partfun1(sK2,X0,X1,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,X0,X2,k1_xboole_0)
% 6.41/1.49      | v1_funct_2(X2,sK3,X0) != iProver_top
% 6.41/1.49      | v1_funct_2(X1,sK2,X0) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.41/1.49      | v1_funct_1(X1) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top
% 6.41/1.49      | v1_xboole_0(sK3) = iProver_top
% 6.41/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_2254,c_1176]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_4697,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1
% 6.41/1.49      | k2_partfun1(sK3,X0,X2,k1_xboole_0) != k2_partfun1(sK2,X0,X1,k1_xboole_0)
% 6.41/1.49      | v1_funct_2(X2,sK3,X0) != iProver_top
% 6.41/1.49      | v1_funct_2(X1,sK2,X0) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_funct_1(X1) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top
% 6.41/1.49      | v1_xboole_0(sK3) = iProver_top
% 6.41/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 6.41/1.49      inference(light_normalisation,[status(thm)],[c_4496,c_2254]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_33,plain,
% 6.41/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_27,negated_conjecture,
% 6.41/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 6.41/1.49      inference(cnf_transformation,[],[f61]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_34,plain,
% 6.41/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_35,plain,
% 6.41/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_36,plain,
% 6.41/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12230,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1
% 6.41/1.49      | k2_partfun1(sK3,X0,X2,k1_xboole_0) != k2_partfun1(sK2,X0,X1,k1_xboole_0)
% 6.41/1.49      | v1_funct_2(X2,sK3,X0) != iProver_top
% 6.41/1.49      | v1_funct_2(X1,sK2,X0) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_funct_1(X1) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_4697,c_33,c_34,c_35,c_36]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12245,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
% 6.41/1.49      | k2_partfun1(sK2,sK1,X0,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 6.41/1.49      | v1_funct_2(X0,sK2,sK1) != iProver_top
% 6.41/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top
% 6.41/1.49      | v1_funct_1(sK5) != iProver_top
% 6.41/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_2503,c_12230]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_9,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | v1_relat_1(X0) ),
% 6.41/1.49      inference(cnf_transformation,[],[f50]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_6,plain,
% 6.41/1.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.41/1.49      inference(cnf_transformation,[],[f47]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_393,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.41/1.49      inference(resolution,[status(thm)],[c_9,c_6]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_977,plain,
% 6.41/1.49      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2035,plain,
% 6.41/1.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_991,c_977]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12246,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
% 6.41/1.49      | k2_partfun1(sK2,sK1,X0,k1_xboole_0) != k1_xboole_0
% 6.41/1.49      | v1_funct_2(X0,sK2,sK1) != iProver_top
% 6.41/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top
% 6.41/1.49      | v1_funct_1(sK5) != iProver_top
% 6.41/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 6.41/1.49      inference(light_normalisation,[status(thm)],[c_12245,c_2035]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_29,negated_conjecture,
% 6.41/1.49      ( ~ v1_xboole_0(sK1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f59]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_32,plain,
% 6.41/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_41,plain,
% 6.41/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_19,negated_conjecture,
% 6.41/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f69]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_42,plain,
% 6.41/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_43,plain,
% 6.41/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12263,plain,
% 6.41/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
% 6.41/1.49      | k2_partfun1(sK2,sK1,X0,k1_xboole_0) != k1_xboole_0
% 6.41/1.49      | v1_funct_2(X0,sK2,sK1) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_12246,c_32,c_41,c_42,c_43]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12264,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
% 6.41/1.49      | k2_partfun1(sK2,sK1,X0,k1_xboole_0) != k1_xboole_0
% 6.41/1.49      | v1_funct_2(X0,sK2,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top ),
% 6.41/1.49      inference(renaming,[status(thm)],[c_12263]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12274,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.41/1.49      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 6.41/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(sK4) != iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_2510,c_12264]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2036,plain,
% 6.41/1.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_988,c_977]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12275,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.41/1.49      | k1_xboole_0 != k1_xboole_0
% 6.41/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(sK4) != iProver_top ),
% 6.41/1.49      inference(light_normalisation,[status(thm)],[c_12274,c_2036]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12276,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.41/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(sK4) != iProver_top ),
% 6.41/1.49      inference(equality_resolution_simp,[status(thm)],[c_12275]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_994,plain,
% 6.41/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.41/1.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.41/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 6.41/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top
% 6.41/1.49      | v1_funct_1(X3) != iProver_top
% 6.41/1.49      | v1_xboole_0(X5) = iProver_top
% 6.41/1.49      | v1_xboole_0(X2) = iProver_top
% 6.41/1.49      | v1_xboole_0(X4) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1121,plain,
% 6.41/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.41/1.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.41/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 6.41/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top
% 6.41/1.49      | v1_funct_1(X3) != iProver_top
% 6.41/1.49      | v1_xboole_0(X2) = iProver_top
% 6.41/1.49      | v1_xboole_0(X4) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.41/1.49      inference(forward_subsumption_resolution,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_994,c_997]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_3046,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 6.41/1.49      | v1_funct_2(X5,X2,X3) != iProver_top
% 6.41/1.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 6.41/1.49      | v1_funct_1(X5) != iProver_top
% 6.41/1.49      | v1_funct_1(X4) != iProver_top
% 6.41/1.49      | v1_funct_1(k1_tmap_1(X0,X3,X1,X2,X4,X5)) != iProver_top
% 6.41/1.49      | v1_xboole_0(X3) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top
% 6.41/1.49      | v1_xboole_0(X2) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_1121,c_996]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_992,plain,
% 6.41/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.41/1.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.41/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top
% 6.41/1.49      | v1_funct_1(X3) != iProver_top
% 6.41/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 6.41/1.49      | v1_xboole_0(X5) = iProver_top
% 6.41/1.49      | v1_xboole_0(X2) = iProver_top
% 6.41/1.49      | v1_xboole_0(X4) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1069,plain,
% 6.41/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.41/1.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.41/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top
% 6.41/1.49      | v1_funct_1(X3) != iProver_top
% 6.41/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 6.41/1.49      | v1_xboole_0(X2) = iProver_top
% 6.41/1.49      | v1_xboole_0(X4) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.41/1.49      inference(forward_subsumption_resolution,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_992,c_997]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5063,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 6.41/1.49      | v1_funct_2(X5,X2,X3) != iProver_top
% 6.41/1.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 6.41/1.49      | v1_funct_1(X5) != iProver_top
% 6.41/1.49      | v1_funct_1(X4) != iProver_top
% 6.41/1.49      | v1_xboole_0(X2) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top
% 6.41/1.49      | v1_xboole_0(X3) = iProver_top ),
% 6.41/1.49      inference(forward_subsumption_resolution,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_3046,c_1069]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5068,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
% 6.41/1.49      | v1_funct_2(X2,X1,sK1) != iProver_top
% 6.41/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_funct_1(sK5) != iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top
% 6.41/1.49      | v1_xboole_0(sK1) = iProver_top
% 6.41/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_991,c_5063]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5303,plain,
% 6.41/1.49      ( v1_funct_1(X2) != iProver_top
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
% 6.41/1.49      | v1_funct_2(X2,X1,sK1) != iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_5068,c_32,c_35,c_41,c_42]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5304,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
% 6.41/1.49      | v1_funct_2(X2,X1,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.41/1.49      inference(renaming,[status(thm)],[c_5303]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5318,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
% 6.41/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | v1_funct_1(sK4) != iProver_top
% 6.41/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_988,c_5304]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_38,plain,
% 6.41/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_22,negated_conjecture,
% 6.41/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f66]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_39,plain,
% 6.41/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5671,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_5318,c_33,c_38,c_39]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5680,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0)
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_985,c_5671]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5777,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_5680,c_34]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12277,plain,
% 6.41/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.41/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(sK4) != iProver_top ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_12276,c_5777]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12,plain,
% 6.41/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_1(X3)
% 6.41/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X1)
% 6.41/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.41/1.49      inference(cnf_transformation,[],[f76]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_171,plain,
% 6.41/1.49      ( ~ v1_funct_1(X3)
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X1)
% 6.41/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_12,c_16,c_15,c_14]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_172,plain,
% 6.41/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.41/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.41/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.49      | ~ v1_funct_1(X0)
% 6.41/1.49      | ~ v1_funct_1(X3)
% 6.41/1.49      | v1_xboole_0(X1)
% 6.41/1.49      | v1_xboole_0(X2)
% 6.41/1.49      | v1_xboole_0(X4)
% 6.41/1.49      | v1_xboole_0(X5)
% 6.41/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.41/1.49      inference(renaming,[status(thm)],[c_171]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_978,plain,
% 6.41/1.49      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 6.41/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.41/1.49      | v1_funct_2(X5,X4,X1) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_funct_1(X5) != iProver_top
% 6.41/1.49      | v1_xboole_0(X3) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top
% 6.41/1.49      | v1_xboole_0(X4) = iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_172]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1148,plain,
% 6.41/1.49      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
% 6.41/1.49      | v1_funct_2(X5,X4,X1) != iProver_top
% 6.41/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 6.41/1.49      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 6.41/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 6.41/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X5) != iProver_top
% 6.41/1.49      | v1_funct_1(X2) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top
% 6.41/1.49      | v1_xboole_0(X4) = iProver_top ),
% 6.41/1.49      inference(forward_subsumption_resolution,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_978,c_997]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_3757,plain,
% 6.41/1.49      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 6.41/1.49      | v1_funct_2(X1,X0,sK1) != iProver_top
% 6.41/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 6.41/1.49      | v1_funct_1(X1) != iProver_top
% 6.41/1.49      | v1_funct_1(sK4) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top
% 6.41/1.49      | v1_xboole_0(sK1) = iProver_top
% 6.41/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_2510,c_1148]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_40,plain,
% 6.41/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_10941,plain,
% 6.41/1.49      ( v1_funct_1(X1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 6.41/1.49      | v1_funct_2(X1,X0,sK1) != iProver_top
% 6.41/1.49      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 6.41/1.49      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_3757,c_32,c_33,c_38,c_39,c_40]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_10942,plain,
% 6.41/1.49      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 6.41/1.49      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 6.41/1.49      | v1_funct_2(X1,X0,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 6.41/1.49      | v1_funct_1(X1) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.49      inference(renaming,[status(thm)],[c_10941]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_10961,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
% 6.41/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0,k1_xboole_0)
% 6.41/1.49      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top
% 6.41/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_2254,c_10942]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_11088,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
% 6.41/1.49      | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
% 6.41/1.49      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.41/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top
% 6.41/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.41/1.49      inference(light_normalisation,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_10961,c_2036,c_2254]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_11560,plain,
% 6.41/1.49      ( v1_funct_1(X0) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 6.41/1.49      | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
% 6.41/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0 ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_11088,c_34,c_35,c_36]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_11561,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
% 6.41/1.49      | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
% 6.41/1.49      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(X0) != iProver_top ),
% 6.41/1.49      inference(renaming,[status(thm)],[c_11560]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_11571,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.41/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 6.41/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_2503,c_11561]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_11572,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.41/1.49      | k1_xboole_0 != k1_xboole_0
% 6.41/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.41/1.49      inference(light_normalisation,[status(thm)],[c_11571,c_2035]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_11573,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.41/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.41/1.49      inference(equality_resolution_simp,[status(thm)],[c_11572]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_11574,plain,
% 6.41/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.41/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.41/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.41/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_11573,c_5777]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_17,negated_conjecture,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.41/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.41/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.41/1.49      inference(cnf_transformation,[],[f71]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2319,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.41/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.41/1.49      | k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_2254,c_17]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2507,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.41/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.41/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_2503,c_2319]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2508,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.41/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.41/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k1_xboole_0 ),
% 6.41/1.49      inference(light_normalisation,[status(thm)],[c_2507,c_2035]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2660,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.41/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.41/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_2508,c_2036,c_2510]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2661,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.41/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 6.41/1.49      inference(equality_resolution_simp,[status(thm)],[c_2660]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5781,plain,
% 6.41/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.41/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_5777,c_2661]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_5782,plain,
% 6.41/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.41/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_5781,c_5777]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(contradiction,plain,
% 6.41/1.49      ( $false ),
% 6.41/1.49      inference(minisat,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_12277,c_11574,c_5782,c_43,c_42,c_41,c_40,c_39,c_38]) ).
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.41/1.49  
% 6.41/1.49  ------                               Statistics
% 6.41/1.49  
% 6.41/1.49  ------ General
% 6.41/1.49  
% 6.41/1.49  abstr_ref_over_cycles:                  0
% 6.41/1.49  abstr_ref_under_cycles:                 0
% 6.41/1.49  gc_basic_clause_elim:                   0
% 6.41/1.49  forced_gc_time:                         0
% 6.41/1.49  parsing_time:                           0.012
% 6.41/1.49  unif_index_cands_time:                  0.
% 6.41/1.49  unif_index_add_time:                    0.
% 6.41/1.49  orderings_time:                         0.
% 6.41/1.49  out_proof_time:                         0.016
% 6.41/1.49  total_time:                             0.675
% 6.41/1.49  num_of_symbols:                         53
% 6.41/1.49  num_of_terms:                           27317
% 6.41/1.49  
% 6.41/1.49  ------ Preprocessing
% 6.41/1.49  
% 6.41/1.49  num_of_splits:                          0
% 6.41/1.49  num_of_split_atoms:                     0
% 6.41/1.49  num_of_reused_defs:                     0
% 6.41/1.49  num_eq_ax_congr_red:                    6
% 6.41/1.49  num_of_sem_filtered_clauses:            1
% 6.41/1.49  num_of_subtypes:                        0
% 6.41/1.49  monotx_restored_types:                  0
% 6.41/1.49  sat_num_of_epr_types:                   0
% 6.41/1.49  sat_num_of_non_cyclic_types:            0
% 6.41/1.49  sat_guarded_non_collapsed_types:        0
% 6.41/1.49  num_pure_diseq_elim:                    0
% 6.41/1.49  simp_replaced_by:                       0
% 6.41/1.49  res_preprocessed:                       138
% 6.41/1.49  prep_upred:                             0
% 6.41/1.49  prep_unflattend:                        6
% 6.41/1.49  smt_new_axioms:                         0
% 6.41/1.49  pred_elim_cands:                        4
% 6.41/1.49  pred_elim:                              3
% 6.41/1.49  pred_elim_cl:                           5
% 6.41/1.49  pred_elim_cycles:                       5
% 6.41/1.49  merged_defs:                            2
% 6.41/1.49  merged_defs_ncl:                        0
% 6.41/1.49  bin_hyper_res:                          2
% 6.41/1.49  prep_cycles:                            4
% 6.41/1.49  pred_elim_time:                         0.002
% 6.41/1.49  splitting_time:                         0.
% 6.41/1.49  sem_filter_time:                        0.
% 6.41/1.49  monotx_time:                            0.001
% 6.41/1.49  subtype_inf_time:                       0.
% 6.41/1.49  
% 6.41/1.49  ------ Problem properties
% 6.41/1.49  
% 6.41/1.49  clauses:                                26
% 6.41/1.49  conjectures:                            13
% 6.41/1.49  epr:                                    8
% 6.41/1.49  horn:                                   20
% 6.41/1.49  ground:                                 14
% 6.41/1.49  unary:                                  15
% 6.41/1.49  binary:                                 2
% 6.41/1.49  lits:                                   112
% 6.41/1.49  lits_eq:                                15
% 6.41/1.49  fd_pure:                                0
% 6.41/1.49  fd_pseudo:                              0
% 6.41/1.49  fd_cond:                                0
% 6.41/1.49  fd_pseudo_cond:                         0
% 6.41/1.49  ac_symbols:                             0
% 6.41/1.49  
% 6.41/1.49  ------ Propositional Solver
% 6.41/1.49  
% 6.41/1.49  prop_solver_calls:                      27
% 6.41/1.49  prop_fast_solver_calls:                 1950
% 6.41/1.49  smt_solver_calls:                       0
% 6.41/1.49  smt_fast_solver_calls:                  0
% 6.41/1.49  prop_num_of_clauses:                    4996
% 6.41/1.49  prop_preprocess_simplified:             9380
% 6.41/1.49  prop_fo_subsumed:                       138
% 6.41/1.49  prop_solver_time:                       0.
% 6.41/1.49  smt_solver_time:                        0.
% 6.41/1.49  smt_fast_solver_time:                   0.
% 6.41/1.49  prop_fast_solver_time:                  0.
% 6.41/1.49  prop_unsat_core_time:                   0.
% 6.41/1.49  
% 6.41/1.49  ------ QBF
% 6.41/1.49  
% 6.41/1.49  qbf_q_res:                              0
% 6.41/1.49  qbf_num_tautologies:                    0
% 6.41/1.49  qbf_prep_cycles:                        0
% 6.41/1.49  
% 6.41/1.49  ------ BMC1
% 6.41/1.49  
% 6.41/1.49  bmc1_current_bound:                     -1
% 6.41/1.49  bmc1_last_solved_bound:                 -1
% 6.41/1.49  bmc1_unsat_core_size:                   -1
% 6.41/1.49  bmc1_unsat_core_parents_size:           -1
% 6.41/1.49  bmc1_merge_next_fun:                    0
% 6.41/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.41/1.49  
% 6.41/1.49  ------ Instantiation
% 6.41/1.49  
% 6.41/1.49  inst_num_of_clauses:                    1141
% 6.41/1.49  inst_num_in_passive:                    183
% 6.41/1.49  inst_num_in_active:                     527
% 6.41/1.49  inst_num_in_unprocessed:                431
% 6.41/1.49  inst_num_of_loops:                      530
% 6.41/1.49  inst_num_of_learning_restarts:          0
% 6.41/1.49  inst_num_moves_active_passive:          1
% 6.41/1.49  inst_lit_activity:                      0
% 6.41/1.49  inst_lit_activity_moves:                0
% 6.41/1.49  inst_num_tautologies:                   0
% 6.41/1.49  inst_num_prop_implied:                  0
% 6.41/1.49  inst_num_existing_simplified:           0
% 6.41/1.49  inst_num_eq_res_simplified:             0
% 6.41/1.49  inst_num_child_elim:                    0
% 6.41/1.49  inst_num_of_dismatching_blockings:      45
% 6.41/1.49  inst_num_of_non_proper_insts:           699
% 6.41/1.49  inst_num_of_duplicates:                 0
% 6.41/1.49  inst_inst_num_from_inst_to_res:         0
% 6.41/1.49  inst_dismatching_checking_time:         0.
% 6.41/1.49  
% 6.41/1.49  ------ Resolution
% 6.41/1.49  
% 6.41/1.49  res_num_of_clauses:                     0
% 6.41/1.49  res_num_in_passive:                     0
% 6.41/1.49  res_num_in_active:                      0
% 6.41/1.49  res_num_of_loops:                       142
% 6.41/1.49  res_forward_subset_subsumed:            31
% 6.41/1.49  res_backward_subset_subsumed:           0
% 6.41/1.49  res_forward_subsumed:                   0
% 6.41/1.49  res_backward_subsumed:                  0
% 6.41/1.49  res_forward_subsumption_resolution:     0
% 6.41/1.49  res_backward_subsumption_resolution:    0
% 6.41/1.49  res_clause_to_clause_subsumption:       1318
% 6.41/1.49  res_orphan_elimination:                 0
% 6.41/1.49  res_tautology_del:                      29
% 6.41/1.49  res_num_eq_res_simplified:              0
% 6.41/1.49  res_num_sel_changes:                    0
% 6.41/1.49  res_moves_from_active_to_pass:          0
% 6.41/1.49  
% 6.41/1.49  ------ Superposition
% 6.41/1.49  
% 6.41/1.49  sup_time_total:                         0.
% 6.41/1.49  sup_time_generating:                    0.
% 6.41/1.49  sup_time_sim_full:                      0.
% 6.41/1.49  sup_time_sim_immed:                     0.
% 6.41/1.49  
% 6.41/1.49  sup_num_of_clauses:                     220
% 6.41/1.49  sup_num_in_active:                      101
% 6.41/1.49  sup_num_in_passive:                     119
% 6.41/1.49  sup_num_of_loops:                       104
% 6.41/1.49  sup_fw_superposition:                   166
% 6.41/1.49  sup_bw_superposition:                   45
% 6.41/1.49  sup_immediate_simplified:               58
% 6.41/1.49  sup_given_eliminated:                   0
% 6.41/1.49  comparisons_done:                       0
% 6.41/1.49  comparisons_avoided:                    0
% 6.41/1.49  
% 6.41/1.49  ------ Simplifications
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  sim_fw_subset_subsumed:                 2
% 6.41/1.49  sim_bw_subset_subsumed:                 0
% 6.41/1.49  sim_fw_subsumed:                        5
% 6.41/1.49  sim_bw_subsumed:                        0
% 6.41/1.49  sim_fw_subsumption_res:                 9
% 6.41/1.49  sim_bw_subsumption_res:                 0
% 6.41/1.49  sim_tautology_del:                      0
% 6.41/1.49  sim_eq_tautology_del:                   2
% 6.41/1.49  sim_eq_res_simp:                        5
% 6.41/1.49  sim_fw_demodulated:                     15
% 6.41/1.49  sim_bw_demodulated:                     4
% 6.41/1.49  sim_light_normalised:                   44
% 6.41/1.49  sim_joinable_taut:                      0
% 6.41/1.49  sim_joinable_simp:                      0
% 6.41/1.49  sim_ac_normalised:                      0
% 6.41/1.49  sim_smt_subsumption:                    0
% 6.41/1.49  
%------------------------------------------------------------------------------
