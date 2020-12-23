%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:38 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  205 (2216 expanded)
%              Number of clauses        :  124 ( 521 expanded)
%              Number of leaves         :   20 ( 872 expanded)
%              Depth                    :   26
%              Number of atoms          : 1099 (28571 expanded)
%              Number of equality atoms :  414 (6713 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f50,f49,f48,f47,f46,f45])).

fof(f89,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f72])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f74,plain,(
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

fof(f75,plain,(
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

fof(f76,plain,(
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

fof(f78,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f71])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2072,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2078,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3484,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_2078])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2086,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2082,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3887,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2086,c_2082])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2079,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5956,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_2079])).

cnf(c_6042,plain,
    ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_3484,c_5956])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_537,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(k7_relat_1(X0,X2),X3) = k1_xboole_0
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_5])).

cnf(c_538,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_2056,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_3548,plain,
    ( k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3484,c_2056])).

cnf(c_6166,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6042,c_3548])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_294,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_295,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_374,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_295])).

cnf(c_2058,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_6286,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2086,c_2058])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2069,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2077,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3963,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2069,c_2077])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2509,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2735,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2509])).

cnf(c_4170,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3963,c_31,c_29,c_2735])).

cnf(c_3962,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_2077])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2504,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2725,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_3988,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3962,c_28,c_26,c_2725])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_221,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_24,c_23,c_22])).

cnf(c_222,plain,
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
    inference(renaming,[status(thm)],[c_221])).

cnf(c_2059,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_3994,plain,
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
    inference(superposition,[status(thm)],[c_3988,c_2059])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_50,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7549,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3994,c_40,c_43,c_49,c_50,c_51])).

cnf(c_7550,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7549])).

cnf(c_7565,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4170,c_7550])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_46,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_47,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_48,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7724,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7565,c_41,c_46,c_47,c_48])).

cnf(c_7725,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7724])).

cnf(c_7736,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK2,sK3),sK1,k1_tmap_1(sK3,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK3,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6286,c_7725])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_290,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_16,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_509,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_510,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_512,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_36,c_34])).

cnf(c_567,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_290,c_512])).

cnf(c_568,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_7742,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK2,sK3),sK1,k1_tmap_1(sK3,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK3,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7736,c_568])).

cnf(c_7743,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK2,sK3),sK1,k1_tmap_1(sK3,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7742,c_6286])).

cnf(c_7744,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK2,sK3),sK1,k1_tmap_1(sK3,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7743,c_568])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2066,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2084,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3411,plain,
    ( r1_tarski(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2066,c_2084])).

cnf(c_6290,plain,
    ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_3411,c_2058])).

cnf(c_25,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3992,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_3988,c_25])).

cnf(c_4174,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4170,c_3992])).

cnf(c_6556,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_6290,c_4174])).

cnf(c_6557,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6556,c_568])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f96])).

cnf(c_214,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_24,c_23,c_22])).

cnf(c_215,plain,
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
    inference(renaming,[status(thm)],[c_214])).

cnf(c_2060,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_3993,plain,
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
    inference(superposition,[status(thm)],[c_3988,c_2060])).

cnf(c_5733,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3993,c_40,c_43,c_49,c_50,c_51])).

cnf(c_5734,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5733])).

cnf(c_5749,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4170,c_5734])).

cnf(c_7225,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5749,c_41,c_46,c_47,c_48])).

cnf(c_7226,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7225])).

cnf(c_7236,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6290,c_7226])).

cnf(c_7256,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7236,c_568])).

cnf(c_7257,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7256,c_6290])).

cnf(c_7258,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7257,c_568])).

cnf(c_7265,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7258])).

cnf(c_7296,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7258,c_38,c_35,c_33,c_7265])).

cnf(c_7297,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_7296])).

cnf(c_7735,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6290,c_7725])).

cnf(c_7755,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7735,c_568])).

cnf(c_7756,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7755,c_6290])).

cnf(c_7757,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7756,c_568])).

cnf(c_7764,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7757])).

cnf(c_7766,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7744,c_38,c_35,c_33,c_6557,c_7297,c_7764])).

cnf(c_9652,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6166,c_7766])).

cnf(c_3485,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2069,c_2078])).

cnf(c_6043,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_3485,c_5956])).

cnf(c_3557,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3485,c_2056])).

cnf(c_6168,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6043,c_3557])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9652,c_6168])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.80/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/0.99  
% 3.80/0.99  ------  iProver source info
% 3.80/0.99  
% 3.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/0.99  git: non_committed_changes: false
% 3.80/0.99  git: last_make_outside_of_git: false
% 3.80/0.99  
% 3.80/0.99  ------ 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options
% 3.80/0.99  
% 3.80/0.99  --out_options                           all
% 3.80/0.99  --tptp_safe_out                         true
% 3.80/0.99  --problem_path                          ""
% 3.80/0.99  --include_path                          ""
% 3.80/0.99  --clausifier                            res/vclausify_rel
% 3.80/0.99  --clausifier_options                    --mode clausify
% 3.80/0.99  --stdin                                 false
% 3.80/0.99  --stats_out                             all
% 3.80/0.99  
% 3.80/0.99  ------ General Options
% 3.80/0.99  
% 3.80/0.99  --fof                                   false
% 3.80/0.99  --time_out_real                         305.
% 3.80/0.99  --time_out_virtual                      -1.
% 3.80/0.99  --symbol_type_check                     false
% 3.80/0.99  --clausify_out                          false
% 3.80/0.99  --sig_cnt_out                           false
% 3.80/0.99  --trig_cnt_out                          false
% 3.80/0.99  --trig_cnt_out_tolerance                1.
% 3.80/0.99  --trig_cnt_out_sk_spl                   false
% 3.80/0.99  --abstr_cl_out                          false
% 3.80/0.99  
% 3.80/0.99  ------ Global Options
% 3.80/0.99  
% 3.80/0.99  --schedule                              default
% 3.80/0.99  --add_important_lit                     false
% 3.80/0.99  --prop_solver_per_cl                    1000
% 3.80/0.99  --min_unsat_core                        false
% 3.80/0.99  --soft_assumptions                      false
% 3.80/0.99  --soft_lemma_size                       3
% 3.80/0.99  --prop_impl_unit_size                   0
% 3.80/0.99  --prop_impl_unit                        []
% 3.80/0.99  --share_sel_clauses                     true
% 3.80/0.99  --reset_solvers                         false
% 3.80/0.99  --bc_imp_inh                            [conj_cone]
% 3.80/0.99  --conj_cone_tolerance                   3.
% 3.80/0.99  --extra_neg_conj                        none
% 3.80/0.99  --large_theory_mode                     true
% 3.80/0.99  --prolific_symb_bound                   200
% 3.80/0.99  --lt_threshold                          2000
% 3.80/0.99  --clause_weak_htbl                      true
% 3.80/0.99  --gc_record_bc_elim                     false
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing Options
% 3.80/0.99  
% 3.80/0.99  --preprocessing_flag                    true
% 3.80/0.99  --time_out_prep_mult                    0.1
% 3.80/0.99  --splitting_mode                        input
% 3.80/0.99  --splitting_grd                         true
% 3.80/0.99  --splitting_cvd                         false
% 3.80/0.99  --splitting_cvd_svl                     false
% 3.80/0.99  --splitting_nvd                         32
% 3.80/0.99  --sub_typing                            true
% 3.80/0.99  --prep_gs_sim                           true
% 3.80/0.99  --prep_unflatten                        true
% 3.80/0.99  --prep_res_sim                          true
% 3.80/0.99  --prep_upred                            true
% 3.80/0.99  --prep_sem_filter                       exhaustive
% 3.80/0.99  --prep_sem_filter_out                   false
% 3.80/0.99  --pred_elim                             true
% 3.80/0.99  --res_sim_input                         true
% 3.80/0.99  --eq_ax_congr_red                       true
% 3.80/0.99  --pure_diseq_elim                       true
% 3.80/0.99  --brand_transform                       false
% 3.80/0.99  --non_eq_to_eq                          false
% 3.80/0.99  --prep_def_merge                        true
% 3.80/0.99  --prep_def_merge_prop_impl              false
% 3.80/0.99  --prep_def_merge_mbd                    true
% 3.80/0.99  --prep_def_merge_tr_red                 false
% 3.80/0.99  --prep_def_merge_tr_cl                  false
% 3.80/0.99  --smt_preprocessing                     true
% 3.80/0.99  --smt_ac_axioms                         fast
% 3.80/0.99  --preprocessed_out                      false
% 3.80/0.99  --preprocessed_stats                    false
% 3.80/0.99  
% 3.80/0.99  ------ Abstraction refinement Options
% 3.80/0.99  
% 3.80/0.99  --abstr_ref                             []
% 3.80/0.99  --abstr_ref_prep                        false
% 3.80/0.99  --abstr_ref_until_sat                   false
% 3.80/0.99  --abstr_ref_sig_restrict                funpre
% 3.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.99  --abstr_ref_under                       []
% 3.80/0.99  
% 3.80/0.99  ------ SAT Options
% 3.80/0.99  
% 3.80/0.99  --sat_mode                              false
% 3.80/0.99  --sat_fm_restart_options                ""
% 3.80/0.99  --sat_gr_def                            false
% 3.80/0.99  --sat_epr_types                         true
% 3.80/0.99  --sat_non_cyclic_types                  false
% 3.80/0.99  --sat_finite_models                     false
% 3.80/0.99  --sat_fm_lemmas                         false
% 3.80/0.99  --sat_fm_prep                           false
% 3.80/0.99  --sat_fm_uc_incr                        true
% 3.80/0.99  --sat_out_model                         small
% 3.80/0.99  --sat_out_clauses                       false
% 3.80/0.99  
% 3.80/0.99  ------ QBF Options
% 3.80/0.99  
% 3.80/0.99  --qbf_mode                              false
% 3.80/0.99  --qbf_elim_univ                         false
% 3.80/0.99  --qbf_dom_inst                          none
% 3.80/0.99  --qbf_dom_pre_inst                      false
% 3.80/0.99  --qbf_sk_in                             false
% 3.80/0.99  --qbf_pred_elim                         true
% 3.80/0.99  --qbf_split                             512
% 3.80/0.99  
% 3.80/0.99  ------ BMC1 Options
% 3.80/0.99  
% 3.80/0.99  --bmc1_incremental                      false
% 3.80/0.99  --bmc1_axioms                           reachable_all
% 3.80/0.99  --bmc1_min_bound                        0
% 3.80/0.99  --bmc1_max_bound                        -1
% 3.80/0.99  --bmc1_max_bound_default                -1
% 3.80/0.99  --bmc1_symbol_reachability              true
% 3.80/0.99  --bmc1_property_lemmas                  false
% 3.80/0.99  --bmc1_k_induction                      false
% 3.80/0.99  --bmc1_non_equiv_states                 false
% 3.80/0.99  --bmc1_deadlock                         false
% 3.80/0.99  --bmc1_ucm                              false
% 3.80/0.99  --bmc1_add_unsat_core                   none
% 3.80/0.99  --bmc1_unsat_core_children              false
% 3.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.99  --bmc1_out_stat                         full
% 3.80/0.99  --bmc1_ground_init                      false
% 3.80/0.99  --bmc1_pre_inst_next_state              false
% 3.80/0.99  --bmc1_pre_inst_state                   false
% 3.80/0.99  --bmc1_pre_inst_reach_state             false
% 3.80/0.99  --bmc1_out_unsat_core                   false
% 3.80/0.99  --bmc1_aig_witness_out                  false
% 3.80/0.99  --bmc1_verbose                          false
% 3.80/0.99  --bmc1_dump_clauses_tptp                false
% 3.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.99  --bmc1_dump_file                        -
% 3.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.99  --bmc1_ucm_extend_mode                  1
% 3.80/0.99  --bmc1_ucm_init_mode                    2
% 3.80/0.99  --bmc1_ucm_cone_mode                    none
% 3.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.99  --bmc1_ucm_relax_model                  4
% 3.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.99  --bmc1_ucm_layered_model                none
% 3.80/0.99  --bmc1_ucm_max_lemma_size               10
% 3.80/0.99  
% 3.80/0.99  ------ AIG Options
% 3.80/0.99  
% 3.80/0.99  --aig_mode                              false
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation Options
% 3.80/0.99  
% 3.80/0.99  --instantiation_flag                    true
% 3.80/0.99  --inst_sos_flag                         false
% 3.80/0.99  --inst_sos_phase                        true
% 3.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel_side                     num_symb
% 3.80/0.99  --inst_solver_per_active                1400
% 3.80/0.99  --inst_solver_calls_frac                1.
% 3.80/0.99  --inst_passive_queue_type               priority_queues
% 3.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.99  --inst_passive_queues_freq              [25;2]
% 3.80/0.99  --inst_dismatching                      true
% 3.80/0.99  --inst_eager_unprocessed_to_passive     true
% 3.80/0.99  --inst_prop_sim_given                   true
% 3.80/0.99  --inst_prop_sim_new                     false
% 3.80/0.99  --inst_subs_new                         false
% 3.80/0.99  --inst_eq_res_simp                      false
% 3.80/0.99  --inst_subs_given                       false
% 3.80/0.99  --inst_orphan_elimination               true
% 3.80/0.99  --inst_learning_loop_flag               true
% 3.80/0.99  --inst_learning_start                   3000
% 3.80/0.99  --inst_learning_factor                  2
% 3.80/0.99  --inst_start_prop_sim_after_learn       3
% 3.80/0.99  --inst_sel_renew                        solver
% 3.80/0.99  --inst_lit_activity_flag                true
% 3.80/0.99  --inst_restr_to_given                   false
% 3.80/0.99  --inst_activity_threshold               500
% 3.80/0.99  --inst_out_proof                        true
% 3.80/0.99  
% 3.80/0.99  ------ Resolution Options
% 3.80/0.99  
% 3.80/0.99  --resolution_flag                       true
% 3.80/0.99  --res_lit_sel                           adaptive
% 3.80/0.99  --res_lit_sel_side                      none
% 3.80/0.99  --res_ordering                          kbo
% 3.80/0.99  --res_to_prop_solver                    active
% 3.80/0.99  --res_prop_simpl_new                    false
% 3.80/0.99  --res_prop_simpl_given                  true
% 3.80/0.99  --res_passive_queue_type                priority_queues
% 3.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.99  --res_passive_queues_freq               [15;5]
% 3.80/0.99  --res_forward_subs                      full
% 3.80/0.99  --res_backward_subs                     full
% 3.80/0.99  --res_forward_subs_resolution           true
% 3.80/0.99  --res_backward_subs_resolution          true
% 3.80/0.99  --res_orphan_elimination                true
% 3.80/0.99  --res_time_limit                        2.
% 3.80/0.99  --res_out_proof                         true
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Options
% 3.80/0.99  
% 3.80/0.99  --superposition_flag                    true
% 3.80/0.99  --sup_passive_queue_type                priority_queues
% 3.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.99  --demod_completeness_check              fast
% 3.80/0.99  --demod_use_ground                      true
% 3.80/0.99  --sup_to_prop_solver                    passive
% 3.80/0.99  --sup_prop_simpl_new                    true
% 3.80/0.99  --sup_prop_simpl_given                  true
% 3.80/0.99  --sup_fun_splitting                     false
% 3.80/0.99  --sup_smt_interval                      50000
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Simplification Setup
% 3.80/0.99  
% 3.80/0.99  --sup_indices_passive                   []
% 3.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/0.99  --sup_full_bw                           [BwDemod]
% 3.80/0.99  --sup_immed_triv                        [TrivRules]
% 3.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/0.99  --sup_immed_bw_main                     []
% 3.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/0.99  
% 3.80/0.99  ------ Combination Options
% 3.80/0.99  
% 3.80/0.99  --comb_res_mult                         3
% 3.80/0.99  --comb_sup_mult                         2
% 3.80/0.99  --comb_inst_mult                        10
% 3.80/0.99  
% 3.80/0.99  ------ Debug Options
% 3.80/0.99  
% 3.80/0.99  --dbg_backtrace                         false
% 3.80/0.99  --dbg_dump_prop_clauses                 false
% 3.80/0.99  --dbg_dump_prop_clauses_file            -
% 3.80/0.99  --dbg_out_stat                          false
% 3.80/0.99  ------ Parsing...
% 3.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/0.99  ------ Proving...
% 3.80/0.99  ------ Problem Properties 
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  clauses                                 36
% 3.80/0.99  conjectures                             13
% 3.80/0.99  EPR                                     10
% 3.80/0.99  Horn                                    30
% 3.80/0.99  unary                                   16
% 3.80/0.99  binary                                  6
% 3.80/0.99  lits                                    137
% 3.80/0.99  lits eq                                 19
% 3.80/0.99  fd_pure                                 0
% 3.80/0.99  fd_pseudo                               0
% 3.80/0.99  fd_cond                                 0
% 3.80/0.99  fd_pseudo_cond                          1
% 3.80/0.99  AC symbols                              0
% 3.80/0.99  
% 3.80/0.99  ------ Schedule dynamic 5 is on 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  ------ 
% 3.80/0.99  Current options:
% 3.80/0.99  ------ 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options
% 3.80/0.99  
% 3.80/0.99  --out_options                           all
% 3.80/0.99  --tptp_safe_out                         true
% 3.80/0.99  --problem_path                          ""
% 3.80/0.99  --include_path                          ""
% 3.80/0.99  --clausifier                            res/vclausify_rel
% 3.80/0.99  --clausifier_options                    --mode clausify
% 3.80/0.99  --stdin                                 false
% 3.80/0.99  --stats_out                             all
% 3.80/0.99  
% 3.80/0.99  ------ General Options
% 3.80/0.99  
% 3.80/0.99  --fof                                   false
% 3.80/0.99  --time_out_real                         305.
% 3.80/0.99  --time_out_virtual                      -1.
% 3.80/0.99  --symbol_type_check                     false
% 3.80/0.99  --clausify_out                          false
% 3.80/0.99  --sig_cnt_out                           false
% 3.80/0.99  --trig_cnt_out                          false
% 3.80/0.99  --trig_cnt_out_tolerance                1.
% 3.80/0.99  --trig_cnt_out_sk_spl                   false
% 3.80/0.99  --abstr_cl_out                          false
% 3.80/0.99  
% 3.80/0.99  ------ Global Options
% 3.80/0.99  
% 3.80/0.99  --schedule                              default
% 3.80/0.99  --add_important_lit                     false
% 3.80/0.99  --prop_solver_per_cl                    1000
% 3.80/0.99  --min_unsat_core                        false
% 3.80/0.99  --soft_assumptions                      false
% 3.80/0.99  --soft_lemma_size                       3
% 3.80/0.99  --prop_impl_unit_size                   0
% 3.80/0.99  --prop_impl_unit                        []
% 3.80/0.99  --share_sel_clauses                     true
% 3.80/0.99  --reset_solvers                         false
% 3.80/0.99  --bc_imp_inh                            [conj_cone]
% 3.80/0.99  --conj_cone_tolerance                   3.
% 3.80/0.99  --extra_neg_conj                        none
% 3.80/0.99  --large_theory_mode                     true
% 3.80/0.99  --prolific_symb_bound                   200
% 3.80/0.99  --lt_threshold                          2000
% 3.80/0.99  --clause_weak_htbl                      true
% 3.80/0.99  --gc_record_bc_elim                     false
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing Options
% 3.80/0.99  
% 3.80/0.99  --preprocessing_flag                    true
% 3.80/0.99  --time_out_prep_mult                    0.1
% 3.80/0.99  --splitting_mode                        input
% 3.80/0.99  --splitting_grd                         true
% 3.80/0.99  --splitting_cvd                         false
% 3.80/0.99  --splitting_cvd_svl                     false
% 3.80/0.99  --splitting_nvd                         32
% 3.80/0.99  --sub_typing                            true
% 3.80/0.99  --prep_gs_sim                           true
% 3.80/0.99  --prep_unflatten                        true
% 3.80/0.99  --prep_res_sim                          true
% 3.80/0.99  --prep_upred                            true
% 3.80/0.99  --prep_sem_filter                       exhaustive
% 3.80/0.99  --prep_sem_filter_out                   false
% 3.80/0.99  --pred_elim                             true
% 3.80/0.99  --res_sim_input                         true
% 3.80/0.99  --eq_ax_congr_red                       true
% 3.80/0.99  --pure_diseq_elim                       true
% 3.80/0.99  --brand_transform                       false
% 3.80/0.99  --non_eq_to_eq                          false
% 3.80/0.99  --prep_def_merge                        true
% 3.80/0.99  --prep_def_merge_prop_impl              false
% 3.80/0.99  --prep_def_merge_mbd                    true
% 3.80/0.99  --prep_def_merge_tr_red                 false
% 3.80/0.99  --prep_def_merge_tr_cl                  false
% 3.80/0.99  --smt_preprocessing                     true
% 3.80/0.99  --smt_ac_axioms                         fast
% 3.80/0.99  --preprocessed_out                      false
% 3.80/0.99  --preprocessed_stats                    false
% 3.80/0.99  
% 3.80/0.99  ------ Abstraction refinement Options
% 3.80/0.99  
% 3.80/0.99  --abstr_ref                             []
% 3.80/0.99  --abstr_ref_prep                        false
% 3.80/0.99  --abstr_ref_until_sat                   false
% 3.80/0.99  --abstr_ref_sig_restrict                funpre
% 3.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.99  --abstr_ref_under                       []
% 3.80/0.99  
% 3.80/0.99  ------ SAT Options
% 3.80/0.99  
% 3.80/0.99  --sat_mode                              false
% 3.80/0.99  --sat_fm_restart_options                ""
% 3.80/0.99  --sat_gr_def                            false
% 3.80/0.99  --sat_epr_types                         true
% 3.80/0.99  --sat_non_cyclic_types                  false
% 3.80/0.99  --sat_finite_models                     false
% 3.80/0.99  --sat_fm_lemmas                         false
% 3.80/0.99  --sat_fm_prep                           false
% 3.80/0.99  --sat_fm_uc_incr                        true
% 3.80/0.99  --sat_out_model                         small
% 3.80/0.99  --sat_out_clauses                       false
% 3.80/0.99  
% 3.80/0.99  ------ QBF Options
% 3.80/0.99  
% 3.80/0.99  --qbf_mode                              false
% 3.80/0.99  --qbf_elim_univ                         false
% 3.80/0.99  --qbf_dom_inst                          none
% 3.80/0.99  --qbf_dom_pre_inst                      false
% 3.80/0.99  --qbf_sk_in                             false
% 3.80/0.99  --qbf_pred_elim                         true
% 3.80/0.99  --qbf_split                             512
% 3.80/0.99  
% 3.80/0.99  ------ BMC1 Options
% 3.80/0.99  
% 3.80/0.99  --bmc1_incremental                      false
% 3.80/0.99  --bmc1_axioms                           reachable_all
% 3.80/0.99  --bmc1_min_bound                        0
% 3.80/0.99  --bmc1_max_bound                        -1
% 3.80/0.99  --bmc1_max_bound_default                -1
% 3.80/0.99  --bmc1_symbol_reachability              true
% 3.80/0.99  --bmc1_property_lemmas                  false
% 3.80/0.99  --bmc1_k_induction                      false
% 3.80/0.99  --bmc1_non_equiv_states                 false
% 3.80/0.99  --bmc1_deadlock                         false
% 3.80/0.99  --bmc1_ucm                              false
% 3.80/0.99  --bmc1_add_unsat_core                   none
% 3.80/0.99  --bmc1_unsat_core_children              false
% 3.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.99  --bmc1_out_stat                         full
% 3.80/0.99  --bmc1_ground_init                      false
% 3.80/0.99  --bmc1_pre_inst_next_state              false
% 3.80/0.99  --bmc1_pre_inst_state                   false
% 3.80/0.99  --bmc1_pre_inst_reach_state             false
% 3.80/0.99  --bmc1_out_unsat_core                   false
% 3.80/0.99  --bmc1_aig_witness_out                  false
% 3.80/0.99  --bmc1_verbose                          false
% 3.80/0.99  --bmc1_dump_clauses_tptp                false
% 3.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.99  --bmc1_dump_file                        -
% 3.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.99  --bmc1_ucm_extend_mode                  1
% 3.80/0.99  --bmc1_ucm_init_mode                    2
% 3.80/0.99  --bmc1_ucm_cone_mode                    none
% 3.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.99  --bmc1_ucm_relax_model                  4
% 3.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.99  --bmc1_ucm_layered_model                none
% 3.80/0.99  --bmc1_ucm_max_lemma_size               10
% 3.80/0.99  
% 3.80/0.99  ------ AIG Options
% 3.80/0.99  
% 3.80/0.99  --aig_mode                              false
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation Options
% 3.80/0.99  
% 3.80/0.99  --instantiation_flag                    true
% 3.80/0.99  --inst_sos_flag                         false
% 3.80/0.99  --inst_sos_phase                        true
% 3.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel_side                     none
% 3.80/0.99  --inst_solver_per_active                1400
% 3.80/0.99  --inst_solver_calls_frac                1.
% 3.80/0.99  --inst_passive_queue_type               priority_queues
% 3.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.99  --inst_passive_queues_freq              [25;2]
% 3.80/0.99  --inst_dismatching                      true
% 3.80/0.99  --inst_eager_unprocessed_to_passive     true
% 3.80/0.99  --inst_prop_sim_given                   true
% 3.80/0.99  --inst_prop_sim_new                     false
% 3.80/0.99  --inst_subs_new                         false
% 3.80/0.99  --inst_eq_res_simp                      false
% 3.80/0.99  --inst_subs_given                       false
% 3.80/0.99  --inst_orphan_elimination               true
% 3.80/0.99  --inst_learning_loop_flag               true
% 3.80/0.99  --inst_learning_start                   3000
% 3.80/0.99  --inst_learning_factor                  2
% 3.80/0.99  --inst_start_prop_sim_after_learn       3
% 3.80/0.99  --inst_sel_renew                        solver
% 3.80/0.99  --inst_lit_activity_flag                true
% 3.80/0.99  --inst_restr_to_given                   false
% 3.80/0.99  --inst_activity_threshold               500
% 3.80/0.99  --inst_out_proof                        true
% 3.80/0.99  
% 3.80/0.99  ------ Resolution Options
% 3.80/0.99  
% 3.80/0.99  --resolution_flag                       false
% 3.80/0.99  --res_lit_sel                           adaptive
% 3.80/0.99  --res_lit_sel_side                      none
% 3.80/0.99  --res_ordering                          kbo
% 3.80/0.99  --res_to_prop_solver                    active
% 3.80/0.99  --res_prop_simpl_new                    false
% 3.80/0.99  --res_prop_simpl_given                  true
% 3.80/0.99  --res_passive_queue_type                priority_queues
% 3.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.99  --res_passive_queues_freq               [15;5]
% 3.80/0.99  --res_forward_subs                      full
% 3.80/0.99  --res_backward_subs                     full
% 3.80/0.99  --res_forward_subs_resolution           true
% 3.80/0.99  --res_backward_subs_resolution          true
% 3.80/0.99  --res_orphan_elimination                true
% 3.80/0.99  --res_time_limit                        2.
% 3.80/0.99  --res_out_proof                         true
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Options
% 3.80/0.99  
% 3.80/0.99  --superposition_flag                    true
% 3.80/0.99  --sup_passive_queue_type                priority_queues
% 3.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.99  --demod_completeness_check              fast
% 3.80/0.99  --demod_use_ground                      true
% 3.80/0.99  --sup_to_prop_solver                    passive
% 3.80/0.99  --sup_prop_simpl_new                    true
% 3.80/0.99  --sup_prop_simpl_given                  true
% 3.80/0.99  --sup_fun_splitting                     false
% 3.80/0.99  --sup_smt_interval                      50000
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Simplification Setup
% 3.80/0.99  
% 3.80/0.99  --sup_indices_passive                   []
% 3.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/0.99  --sup_full_bw                           [BwDemod]
% 3.80/0.99  --sup_immed_triv                        [TrivRules]
% 3.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/0.99  --sup_immed_bw_main                     []
% 3.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/0.99  
% 3.80/0.99  ------ Combination Options
% 3.80/0.99  
% 3.80/0.99  --comb_res_mult                         3
% 3.80/0.99  --comb_sup_mult                         2
% 3.80/0.99  --comb_inst_mult                        10
% 3.80/0.99  
% 3.80/0.99  ------ Debug Options
% 3.80/0.99  
% 3.80/0.99  --dbg_backtrace                         false
% 3.80/0.99  --dbg_dump_prop_clauses                 false
% 3.80/0.99  --dbg_dump_prop_clauses_file            -
% 3.80/0.99  --dbg_out_stat                          false
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  ------ Proving...
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  % SZS status Theorem for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  fof(f16,conjecture,(
% 3.80/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f17,negated_conjecture,(
% 3.80/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.80/0.99    inference(negated_conjecture,[],[f16])).
% 3.80/0.99  
% 3.80/0.99  fof(f35,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f17])).
% 3.80/0.99  
% 3.80/0.99  fof(f36,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.80/0.99    inference(flattening,[],[f35])).
% 3.80/0.99  
% 3.80/0.99  fof(f50,plain,(
% 3.80/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f49,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f48,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f47,plain,(
% 3.80/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f46,plain,(
% 3.80/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f45,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f51,plain,(
% 3.80/0.99    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f50,f49,f48,f47,f46,f45])).
% 3.80/0.99  
% 3.80/0.99  fof(f89,plain,(
% 3.80/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f12,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f28,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(ennf_transformation,[],[f12])).
% 3.80/0.99  
% 3.80/0.99  fof(f69,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f28])).
% 3.80/0.99  
% 3.80/0.99  fof(f2,axiom,(
% 3.80/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f38,plain,(
% 3.80/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.99    inference(nnf_transformation,[],[f2])).
% 3.80/0.99  
% 3.80/0.99  fof(f39,plain,(
% 3.80/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.99    inference(flattening,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f54,plain,(
% 3.80/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.80/0.99    inference(cnf_transformation,[],[f39])).
% 3.80/0.99  
% 3.80/0.99  fof(f92,plain,(
% 3.80/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.80/0.99    inference(equality_resolution,[],[f54])).
% 3.80/0.99  
% 3.80/0.99  fof(f7,axiom,(
% 3.80/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f21,plain,(
% 3.80/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(ennf_transformation,[],[f7])).
% 3.80/0.99  
% 3.80/0.99  fof(f41,plain,(
% 3.80/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(nnf_transformation,[],[f21])).
% 3.80/0.99  
% 3.80/0.99  fof(f63,plain,(
% 3.80/0.99    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f41])).
% 3.80/0.99  
% 3.80/0.99  fof(f10,axiom,(
% 3.80/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f24,plain,(
% 3.80/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f10])).
% 3.80/0.99  
% 3.80/0.99  fof(f25,plain,(
% 3.80/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(flattening,[],[f24])).
% 3.80/0.99  
% 3.80/0.99  fof(f66,plain,(
% 3.80/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f25])).
% 3.80/0.99  
% 3.80/0.99  fof(f9,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f22,plain,(
% 3.80/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.80/0.99    inference(ennf_transformation,[],[f9])).
% 3.80/0.99  
% 3.80/0.99  fof(f23,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 3.80/0.99    inference(flattening,[],[f22])).
% 3.80/0.99  
% 3.80/0.99  fof(f65,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f23])).
% 3.80/0.99  
% 3.80/0.99  fof(f3,axiom,(
% 3.80/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f57,plain,(
% 3.80/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f3])).
% 3.80/0.99  
% 3.80/0.99  fof(f4,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f18,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.80/0.99    inference(ennf_transformation,[],[f4])).
% 3.80/0.99  
% 3.80/0.99  fof(f58,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f18])).
% 3.80/0.99  
% 3.80/0.99  fof(f5,axiom,(
% 3.80/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f40,plain,(
% 3.80/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.80/0.99    inference(nnf_transformation,[],[f5])).
% 3.80/0.99  
% 3.80/0.99  fof(f60,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f40])).
% 3.80/0.99  
% 3.80/0.99  fof(f86,plain,(
% 3.80/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f13,axiom,(
% 3.80/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f29,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.80/0.99    inference(ennf_transformation,[],[f13])).
% 3.80/0.99  
% 3.80/0.99  fof(f30,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.80/0.99    inference(flattening,[],[f29])).
% 3.80/0.99  
% 3.80/0.99  fof(f70,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f30])).
% 3.80/0.99  
% 3.80/0.99  fof(f84,plain,(
% 3.80/0.99    v1_funct_1(sK4)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f87,plain,(
% 3.80/0.99    v1_funct_1(sK5)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f14,axiom,(
% 3.80/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f31,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f14])).
% 3.80/0.99  
% 3.80/0.99  fof(f32,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.80/0.99    inference(flattening,[],[f31])).
% 3.80/0.99  
% 3.80/0.99  fof(f43,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.80/0.99    inference(nnf_transformation,[],[f32])).
% 3.80/0.99  
% 3.80/0.99  fof(f44,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.80/0.99    inference(flattening,[],[f43])).
% 3.80/0.99  
% 3.80/0.99  fof(f72,plain,(
% 3.80/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f44])).
% 3.80/0.99  
% 3.80/0.99  fof(f95,plain,(
% 3.80/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.80/0.99    inference(equality_resolution,[],[f72])).
% 3.80/0.99  
% 3.80/0.99  fof(f15,axiom,(
% 3.80/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f33,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.80/0.99    inference(ennf_transformation,[],[f15])).
% 3.80/0.99  
% 3.80/0.99  fof(f34,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.80/0.99    inference(flattening,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  fof(f74,plain,(
% 3.80/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f34])).
% 3.80/0.99  
% 3.80/0.99  fof(f75,plain,(
% 3.80/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f34])).
% 3.80/0.99  
% 3.80/0.99  fof(f76,plain,(
% 3.80/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f34])).
% 3.80/0.99  
% 3.80/0.99  fof(f78,plain,(
% 3.80/0.99    ~v1_xboole_0(sK1)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f81,plain,(
% 3.80/0.99    ~v1_xboole_0(sK3)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f88,plain,(
% 3.80/0.99    v1_funct_2(sK5,sK3,sK1)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f79,plain,(
% 3.80/0.99    ~v1_xboole_0(sK2)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f85,plain,(
% 3.80/0.99    v1_funct_2(sK4,sK2,sK1)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f1,axiom,(
% 3.80/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f37,plain,(
% 3.80/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.80/0.99    inference(nnf_transformation,[],[f1])).
% 3.80/0.99  
% 3.80/0.99  fof(f52,plain,(
% 3.80/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f37])).
% 3.80/0.99  
% 3.80/0.99  fof(f11,axiom,(
% 3.80/0.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f26,plain,(
% 3.80/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.80/0.99    inference(ennf_transformation,[],[f11])).
% 3.80/0.99  
% 3.80/0.99  fof(f27,plain,(
% 3.80/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.80/0.99    inference(flattening,[],[f26])).
% 3.80/0.99  
% 3.80/0.99  fof(f42,plain,(
% 3.80/0.99    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.80/0.99    inference(nnf_transformation,[],[f27])).
% 3.80/0.99  
% 3.80/0.99  fof(f67,plain,(
% 3.80/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f42])).
% 3.80/0.99  
% 3.80/0.99  fof(f83,plain,(
% 3.80/0.99    r1_subset_1(sK2,sK3)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f77,plain,(
% 3.80/0.99    ~v1_xboole_0(sK0)),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f80,plain,(
% 3.80/0.99    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f82,plain,(
% 3.80/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f59,plain,(
% 3.80/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f40])).
% 3.80/0.99  
% 3.80/0.99  fof(f90,plain,(
% 3.80/0.99    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 3.80/0.99    inference(cnf_transformation,[],[f51])).
% 3.80/0.99  
% 3.80/0.99  fof(f71,plain,(
% 3.80/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f44])).
% 3.80/0.99  
% 3.80/0.99  fof(f96,plain,(
% 3.80/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.80/0.99    inference(equality_resolution,[],[f71])).
% 3.80/0.99  
% 3.80/0.99  cnf(c_26,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2072,plain,
% 3.80/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_17,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | v1_relat_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2078,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.80/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3484,plain,
% 3.80/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2072,c_2078]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4,plain,
% 3.80/0.99      ( r1_tarski(X0,X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2086,plain,
% 3.80/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10,plain,
% 3.80/0.99      ( v4_relat_1(X0,X1)
% 3.80/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.80/0.99      | ~ v1_relat_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2082,plain,
% 3.80/0.99      ( v4_relat_1(X0,X1) = iProver_top
% 3.80/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3887,plain,
% 3.80/0.99      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2086,c_2082]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14,plain,
% 3.80/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.80/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2079,plain,
% 3.80/0.99      ( k7_relat_1(X0,X1) = X0
% 3.80/0.99      | v4_relat_1(X0,X1) != iProver_top
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5956,plain,
% 3.80/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3887,c_2079]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6042,plain,
% 3.80/0.99      ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3484,c_5956]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_13,plain,
% 3.80/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.80/0.99      | ~ v1_relat_1(X2)
% 3.80/0.99      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 3.80/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5,plain,
% 3.80/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_537,plain,
% 3.80/0.99      ( ~ v1_relat_1(X0)
% 3.80/0.99      | X1 != X2
% 3.80/0.99      | k7_relat_1(k7_relat_1(X0,X2),X3) = k1_xboole_0
% 3.80/0.99      | k1_xboole_0 != X3 ),
% 3.80/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_538,plain,
% 3.80/0.99      ( ~ v1_relat_1(X0)
% 3.80/0.99      | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
% 3.80/0.99      inference(unflattening,[status(thm)],[c_537]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2056,plain,
% 3.80/0.99      ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3548,plain,
% 3.80/0.99      ( k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k1_xboole_0 ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3484,c_2056]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6166,plain,
% 3.80/0.99      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_6042,c_3548]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.80/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_294,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.80/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_295,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_294]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_374,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.80/0.99      inference(bin_hyper_res,[status(thm)],[c_6,c_295]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2058,plain,
% 3.80/0.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.80/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6286,plain,
% 3.80/0.99      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2086,c_2058]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_29,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2069,plain,
% 3.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_18,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2077,plain,
% 3.80/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.80/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3963,plain,
% 3.80/0.99      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 3.80/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2069,c_2077]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_31,negated_conjecture,
% 3.80/0.99      ( v1_funct_1(sK4) ),
% 3.80/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2509,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ v1_funct_1(sK4)
% 3.80/0.99      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2735,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.80/0.99      | ~ v1_funct_1(sK4)
% 3.80/0.99      | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2509]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4170,plain,
% 3.80/0.99      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3963,c_31,c_29,c_2735]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3962,plain,
% 3.80/0.99      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 3.80/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2072,c_2077]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_28,negated_conjecture,
% 3.80/0.99      ( v1_funct_1(sK5) ),
% 3.80/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2504,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ v1_funct_1(sK5)
% 3.80/0.99      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2725,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.80/0.99      | ~ v1_funct_1(sK5)
% 3.80/0.99      | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2504]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3988,plain,
% 3.80/0.99      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3962,c_28,c_26,c_2725]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_20,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.80/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_24,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_23,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_22,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_221,plain,
% 3.80/0.99      ( ~ v1_funct_1(X3)
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_20,c_24,c_23,c_22]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_222,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_221]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2059,plain,
% 3.80/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.80/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.80/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.80/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.80/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.80/0.99      | v1_funct_1(X2) != iProver_top
% 3.80/0.99      | v1_funct_1(X5) != iProver_top
% 3.80/0.99      | v1_xboole_0(X3) = iProver_top
% 3.80/0.99      | v1_xboole_0(X1) = iProver_top
% 3.80/0.99      | v1_xboole_0(X4) = iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3994,plain,
% 3.80/0.99      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 3.80/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.80/0.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | v1_funct_1(X1) != iProver_top
% 3.80/0.99      | v1_funct_1(sK5) != iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top
% 3.80/0.99      | v1_xboole_0(X2) = iProver_top
% 3.80/0.99      | v1_xboole_0(sK1) = iProver_top
% 3.80/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3988,c_2059]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_37,negated_conjecture,
% 3.80/0.99      ( ~ v1_xboole_0(sK1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_40,plain,
% 3.80/0.99      ( v1_xboole_0(sK1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_34,negated_conjecture,
% 3.80/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_43,plain,
% 3.80/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_49,plain,
% 3.80/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_27,negated_conjecture,
% 3.80/0.99      ( v1_funct_2(sK5,sK3,sK1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_50,plain,
% 3.80/0.99      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_51,plain,
% 3.80/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7549,plain,
% 3.80/0.99      ( v1_funct_1(X1) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.80/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 3.80/0.99      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top
% 3.80/0.99      | v1_xboole_0(X2) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3994,c_40,c_43,c_49,c_50,c_51]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7550,plain,
% 3.80/0.99      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 3.80/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | v1_funct_1(X1) != iProver_top
% 3.80/0.99      | v1_xboole_0(X2) = iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_7549]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7565,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.80/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.80/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | v1_funct_1(sK4) != iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top
% 3.80/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_4170,c_7550]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_36,negated_conjecture,
% 3.80/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.80/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_41,plain,
% 3.80/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_46,plain,
% 3.80/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_30,negated_conjecture,
% 3.80/0.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_47,plain,
% 3.80/0.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_48,plain,
% 3.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7724,plain,
% 3.80/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.80/0.99      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_7565,c_41,c_46,c_47,c_48]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7725,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_7724]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7736,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK3,sK2,sK3),sK1,k1_tmap_1(sK3,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k9_subset_1(sK3,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_6286,c_7725]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1,plain,
% 3.80/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.80/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_290,plain,
% 3.80/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.80/0.99      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_16,plain,
% 3.80/0.99      ( ~ r1_subset_1(X0,X1)
% 3.80/0.99      | r1_xboole_0(X0,X1)
% 3.80/0.99      | v1_xboole_0(X0)
% 3.80/0.99      | v1_xboole_0(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_32,negated_conjecture,
% 3.80/0.99      ( r1_subset_1(sK2,sK3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_509,plain,
% 3.80/0.99      ( r1_xboole_0(X0,X1)
% 3.80/0.99      | v1_xboole_0(X0)
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | sK3 != X1
% 3.80/0.99      | sK2 != X0 ),
% 3.80/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_510,plain,
% 3.80/0.99      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 3.80/0.99      inference(unflattening,[status(thm)],[c_509]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_512,plain,
% 3.80/0.99      ( r1_xboole_0(sK2,sK3) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_510,c_36,c_34]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_567,plain,
% 3.80/0.99      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 3.80/0.99      inference(resolution_lifted,[status(thm)],[c_290,c_512]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_568,plain,
% 3.80/0.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.80/0.99      inference(unflattening,[status(thm)],[c_567]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7742,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK3,sK2,sK3),sK1,k1_tmap_1(sK3,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k9_subset_1(sK3,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_7736,c_568]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7743,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK3,sK2,sK3),sK1,k1_tmap_1(sK3,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7742,c_6286]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7744,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK3,sK2,sK3),sK1,k1_tmap_1(sK3,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_7743,c_568]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_38,negated_conjecture,
% 3.80/0.99      ( ~ v1_xboole_0(sK0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_35,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_33,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2066,plain,
% 3.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2084,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.80/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3411,plain,
% 3.80/0.99      ( r1_tarski(sK3,sK0) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2066,c_2084]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6290,plain,
% 3.80/0.99      ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3411,c_2058]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_25,negated_conjecture,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.80/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.80/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3992,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.80/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.80/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_3988,c_25]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4174,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.80/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.80/0.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_4170,c_3992]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6556,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.80/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.80/0.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_6290,c_4174]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6557,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.80/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.80/0.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_6556,c_568]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_21,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.80/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_214,plain,
% 3.80/0.99      ( ~ v1_funct_1(X3)
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_21,c_24,c_23,c_22]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_215,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | ~ v1_funct_1(X3)
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | v1_xboole_0(X4)
% 3.80/0.99      | v1_xboole_0(X5)
% 3.80/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_214]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2060,plain,
% 3.80/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.80/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.80/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.80/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.80/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.80/0.99      | v1_funct_1(X2) != iProver_top
% 3.80/0.99      | v1_funct_1(X5) != iProver_top
% 3.80/0.99      | v1_xboole_0(X3) = iProver_top
% 3.80/0.99      | v1_xboole_0(X1) = iProver_top
% 3.80/0.99      | v1_xboole_0(X4) = iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3993,plain,
% 3.80/0.99      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 3.80/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.80/0.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | v1_funct_1(X1) != iProver_top
% 3.80/0.99      | v1_funct_1(sK5) != iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top
% 3.80/0.99      | v1_xboole_0(X2) = iProver_top
% 3.80/0.99      | v1_xboole_0(sK1) = iProver_top
% 3.80/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3988,c_2060]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5733,plain,
% 3.80/0.99      ( v1_funct_1(X1) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.80/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 3.80/0.99      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top
% 3.80/0.99      | v1_xboole_0(X2) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3993,c_40,c_43,c_49,c_50,c_51]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5734,plain,
% 3.80/0.99      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.80/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 3.80/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.80/0.99      | v1_funct_1(X1) != iProver_top
% 3.80/0.99      | v1_xboole_0(X2) = iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_5733]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5749,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.80/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.80/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | v1_funct_1(sK4) != iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top
% 3.80/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_4170,c_5734]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7225,plain,
% 3.80/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.80/0.99      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_5749,c_41,c_46,c_47,c_48]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7226,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_7225]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7236,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_6290,c_7226]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7256,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_7236,c_568]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7257,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7256,c_6290]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7258,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_7257,c_568]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7265,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 3.80/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 3.80/0.99      | v1_xboole_0(sK0)
% 3.80/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7258]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7296,plain,
% 3.80/0.99      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_7258,c_38,c_35,c_33,c_7265]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7297,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.80/0.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_7296]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7735,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_6290,c_7725]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7755,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_7735,c_568]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7756,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_7755,c_6290]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7757,plain,
% 3.80/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.80/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_7756,c_568]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7764,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 3.80/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 3.80/0.99      | v1_xboole_0(sK0)
% 3.80/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.80/0.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7757]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7766,plain,
% 3.80/0.99      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_7744,c_38,c_35,c_33,c_6557,c_7297,c_7764]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9652,plain,
% 3.80/0.99      ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_6166,c_7766]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3485,plain,
% 3.80/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2069,c_2078]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6043,plain,
% 3.80/0.99      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3485,c_5956]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3557,plain,
% 3.80/0.99      ( k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k1_xboole_0 ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3485,c_2056]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6168,plain,
% 3.80/0.99      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_6043,c_3557]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(contradiction,plain,
% 3.80/0.99      ( $false ),
% 3.80/0.99      inference(minisat,[status(thm)],[c_9652,c_6168]) ).
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  ------                               Statistics
% 3.80/0.99  
% 3.80/0.99  ------ General
% 3.80/0.99  
% 3.80/0.99  abstr_ref_over_cycles:                  0
% 3.80/0.99  abstr_ref_under_cycles:                 0
% 3.80/0.99  gc_basic_clause_elim:                   0
% 3.80/0.99  forced_gc_time:                         0
% 3.80/0.99  parsing_time:                           0.014
% 3.80/0.99  unif_index_cands_time:                  0.
% 3.80/0.99  unif_index_add_time:                    0.
% 3.80/0.99  orderings_time:                         0.
% 3.80/0.99  out_proof_time:                         0.017
% 3.80/0.99  total_time:                             0.422
% 3.80/0.99  num_of_symbols:                         56
% 3.80/0.99  num_of_terms:                           13663
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing
% 3.80/0.99  
% 3.80/0.99  num_of_splits:                          0
% 3.80/0.99  num_of_split_atoms:                     0
% 3.80/0.99  num_of_reused_defs:                     0
% 3.80/0.99  num_eq_ax_congr_red:                    16
% 3.80/0.99  num_of_sem_filtered_clauses:            1
% 3.80/0.99  num_of_subtypes:                        0
% 3.80/0.99  monotx_restored_types:                  0
% 3.80/0.99  sat_num_of_epr_types:                   0
% 3.80/0.99  sat_num_of_non_cyclic_types:            0
% 3.80/0.99  sat_guarded_non_collapsed_types:        0
% 3.80/0.99  num_pure_diseq_elim:                    0
% 3.80/0.99  simp_replaced_by:                       0
% 3.80/0.99  res_preprocessed:                       179
% 3.80/0.99  prep_upred:                             0
% 3.80/0.99  prep_unflattend:                        24
% 3.80/0.99  smt_new_axioms:                         0
% 3.80/0.99  pred_elim_cands:                        7
% 3.80/0.99  pred_elim:                              2
% 3.80/0.99  pred_elim_cl:                           2
% 3.80/0.99  pred_elim_cycles:                       4
% 3.80/0.99  merged_defs:                            10
% 3.80/0.99  merged_defs_ncl:                        0
% 3.80/0.99  bin_hyper_res:                          11
% 3.80/0.99  prep_cycles:                            4
% 3.80/0.99  pred_elim_time:                         0.008
% 3.80/0.99  splitting_time:                         0.
% 3.80/0.99  sem_filter_time:                        0.
% 3.80/0.99  monotx_time:                            0.001
% 3.80/0.99  subtype_inf_time:                       0.
% 3.80/0.99  
% 3.80/0.99  ------ Problem properties
% 3.80/0.99  
% 3.80/0.99  clauses:                                36
% 3.80/0.99  conjectures:                            13
% 3.80/0.99  epr:                                    10
% 3.80/0.99  horn:                                   30
% 3.80/0.99  ground:                                 14
% 3.80/0.99  unary:                                  16
% 3.80/0.99  binary:                                 6
% 3.80/0.99  lits:                                   137
% 3.80/0.99  lits_eq:                                19
% 3.80/0.99  fd_pure:                                0
% 3.80/0.99  fd_pseudo:                              0
% 3.80/0.99  fd_cond:                                0
% 3.80/0.99  fd_pseudo_cond:                         1
% 3.80/0.99  ac_symbols:                             0
% 3.80/0.99  
% 3.80/0.99  ------ Propositional Solver
% 3.80/0.99  
% 3.80/0.99  prop_solver_calls:                      27
% 3.80/0.99  prop_fast_solver_calls:                 2020
% 3.80/0.99  smt_solver_calls:                       0
% 3.80/0.99  smt_fast_solver_calls:                  0
% 3.80/0.99  prop_num_of_clauses:                    3365
% 3.80/0.99  prop_preprocess_simplified:             8211
% 3.80/0.99  prop_fo_subsumed:                       97
% 3.80/0.99  prop_solver_time:                       0.
% 3.80/0.99  smt_solver_time:                        0.
% 3.80/0.99  smt_fast_solver_time:                   0.
% 3.80/0.99  prop_fast_solver_time:                  0.
% 3.80/0.99  prop_unsat_core_time:                   0.
% 3.80/0.99  
% 3.80/0.99  ------ QBF
% 3.80/0.99  
% 3.80/0.99  qbf_q_res:                              0
% 3.80/0.99  qbf_num_tautologies:                    0
% 3.80/0.99  qbf_prep_cycles:                        0
% 3.80/0.99  
% 3.80/0.99  ------ BMC1
% 3.80/0.99  
% 3.80/0.99  bmc1_current_bound:                     -1
% 3.80/0.99  bmc1_last_solved_bound:                 -1
% 3.80/0.99  bmc1_unsat_core_size:                   -1
% 3.80/0.99  bmc1_unsat_core_parents_size:           -1
% 3.80/0.99  bmc1_merge_next_fun:                    0
% 3.80/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation
% 3.80/0.99  
% 3.80/0.99  inst_num_of_clauses:                    798
% 3.80/0.99  inst_num_in_passive:                    98
% 3.80/0.99  inst_num_in_active:                     529
% 3.80/0.99  inst_num_in_unprocessed:                173
% 3.80/0.99  inst_num_of_loops:                      540
% 3.80/0.99  inst_num_of_learning_restarts:          0
% 3.80/0.99  inst_num_moves_active_passive:          7
% 3.80/0.99  inst_lit_activity:                      0
% 3.80/0.99  inst_lit_activity_moves:                0
% 3.80/0.99  inst_num_tautologies:                   0
% 3.80/0.99  inst_num_prop_implied:                  0
% 3.80/0.99  inst_num_existing_simplified:           0
% 3.80/0.99  inst_num_eq_res_simplified:             0
% 3.80/0.99  inst_num_child_elim:                    0
% 3.80/0.99  inst_num_of_dismatching_blockings:      174
% 3.80/0.99  inst_num_of_non_proper_insts:           790
% 3.80/0.99  inst_num_of_duplicates:                 0
% 3.80/0.99  inst_inst_num_from_inst_to_res:         0
% 3.80/0.99  inst_dismatching_checking_time:         0.
% 3.80/0.99  
% 3.80/0.99  ------ Resolution
% 3.80/0.99  
% 3.80/0.99  res_num_of_clauses:                     0
% 3.80/0.99  res_num_in_passive:                     0
% 3.80/0.99  res_num_in_active:                      0
% 3.80/0.99  res_num_of_loops:                       183
% 3.80/0.99  res_forward_subset_subsumed:            48
% 3.80/0.99  res_backward_subset_subsumed:           4
% 3.80/0.99  res_forward_subsumed:                   0
% 3.80/0.99  res_backward_subsumed:                  0
% 3.80/0.99  res_forward_subsumption_resolution:     0
% 3.80/0.99  res_backward_subsumption_resolution:    0
% 3.80/0.99  res_clause_to_clause_subsumption:       496
% 3.80/0.99  res_orphan_elimination:                 0
% 3.80/0.99  res_tautology_del:                      54
% 3.80/0.99  res_num_eq_res_simplified:              0
% 3.80/0.99  res_num_sel_changes:                    0
% 3.80/0.99  res_moves_from_active_to_pass:          0
% 3.80/0.99  
% 3.80/0.99  ------ Superposition
% 3.80/0.99  
% 3.80/0.99  sup_time_total:                         0.
% 3.80/0.99  sup_time_generating:                    0.
% 3.80/0.99  sup_time_sim_full:                      0.
% 3.80/0.99  sup_time_sim_immed:                     0.
% 3.80/0.99  
% 3.80/0.99  sup_num_of_clauses:                     167
% 3.80/0.99  sup_num_in_active:                      99
% 3.80/0.99  sup_num_in_passive:                     68
% 3.80/0.99  sup_num_of_loops:                       106
% 3.80/0.99  sup_fw_superposition:                   108
% 3.80/0.99  sup_bw_superposition:                   65
% 3.80/0.99  sup_immediate_simplified:               78
% 3.80/0.99  sup_given_eliminated:                   0
% 3.80/0.99  comparisons_done:                       0
% 3.80/0.99  comparisons_avoided:                    0
% 3.80/0.99  
% 3.80/0.99  ------ Simplifications
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  sim_fw_subset_subsumed:                 2
% 3.80/0.99  sim_bw_subset_subsumed:                 0
% 3.80/0.99  sim_fw_subsumed:                        6
% 3.80/0.99  sim_bw_subsumed:                        5
% 3.80/0.99  sim_fw_subsumption_res:                 2
% 3.80/0.99  sim_bw_subsumption_res:                 1
% 3.80/0.99  sim_tautology_del:                      2
% 3.80/0.99  sim_eq_tautology_del:                   3
% 3.80/0.99  sim_eq_res_simp:                        0
% 3.80/0.99  sim_fw_demodulated:                     47
% 3.80/0.99  sim_bw_demodulated:                     7
% 3.80/0.99  sim_light_normalised:                   33
% 3.80/0.99  sim_joinable_taut:                      0
% 3.80/0.99  sim_joinable_simp:                      0
% 3.80/0.99  sim_ac_normalised:                      0
% 3.80/0.99  sim_smt_subsumption:                    0
% 3.80/0.99  
%------------------------------------------------------------------------------
