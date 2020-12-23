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

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  217 (2267 expanded)
%              Number of clauses        :  143 ( 608 expanded)
%              Number of leaves         :   19 ( 865 expanded)
%              Depth                    :   26
%              Number of atoms          : 1267 (28050 expanded)
%              Number of equality atoms :  574 (6948 expanded)
%              Maximal formula depth    :   25 (   7 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f94,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f95,plain,(
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

cnf(c_845,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1352,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_851,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1347,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_2483,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1347])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1798,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_2014,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_2880,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2483,c_25,c_23,c_2014])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_839,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1358,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_854,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k1_setfam_1(k2_tarski(X2_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1344,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k1_setfam_1(k2_tarski(X1_54,X2_54))
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_2364,plain,
    ( k9_subset_1(sK0,X0_54,sK3) = k1_setfam_1(k2_tarski(X0_54,sK3)) ),
    inference(superposition,[status(thm)],[c_1358,c_1344])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_842,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1355,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_2484,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1347])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1803,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_2019,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_2885,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2484,c_28,c_26,c_2019])).

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
    inference(cnf_transformation,[],[f94])).

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

cnf(c_832,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_196])).

cnf(c_1365,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1345,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_xboole_0(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_1567,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X0_54,X4_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X0_54,X4_54))
    | k2_partfun1(k4_subset_1(X3_54,X0_54,X4_54),X1_54,k1_tmap_1(X3_54,X1_54,X0_54,X4_54,X2_54,X5_54),X4_54) = X5_54
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1365,c_1345])).

cnf(c_6815,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2885,c_1567])).

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

cnf(c_24580,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6815,c_37,c_38,c_43,c_44,c_45])).

cnf(c_24581,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_24580])).

cnf(c_24602,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
    | k2_partfun1(sK3,sK1,X0_54,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_24581])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_252,plain,
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

cnf(c_506,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_507,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_509,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_33,c_31])).

cnf(c_535,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_509])).

cnf(c_536,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_830,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_536])).

cnf(c_24699,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_54,k1_xboole_0)
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24602,c_830])).

cnf(c_24700,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0_54,k1_xboole_0)
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24699,c_2364])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_852,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1346,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_2283,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1346])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_855,plain,
    ( k2_tarski(X0_54,X1_54) = k2_tarski(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_856,plain,
    ( k1_setfam_1(k2_tarski(X0_54,k1_xboole_0)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1955,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0_54)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_855,c_856])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_250,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_520,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_relat_1(X0) != X3
    | k1_setfam_1(k2_tarski(X2,X3)) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_250,c_6])).

cnf(c_521,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X1,k1_relat_1(X0))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_831,plain,
    ( ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X1_54,k1_relat_1(X0_54))) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_1366,plain,
    ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X1_54,k1_relat_1(X0_54))) != k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_2986,plain,
    ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_1366])).

cnf(c_3300,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2283,c_2986])).

cnf(c_24701,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
    | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24700,c_830,c_3300])).

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

cnf(c_24979,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24701,c_39,c_40,c_41])).

cnf(c_24980,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
    | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_24979])).

cnf(c_24990,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2880,c_24980])).

cnf(c_2282,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1346])).

cnf(c_3299,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2282,c_2986])).

cnf(c_24991,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24990,c_3299])).

cnf(c_24992,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_24991])).

cnf(c_849,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1349,plain,
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
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_1512,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1349,c_1345])).

cnf(c_4868,plain,
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
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1347])).

cnf(c_847,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1351,plain,
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
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_1460,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1351,c_1345])).

cnf(c_9692,plain,
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
    | v1_xboole_0(X3_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4868,c_1460])).

cnf(c_9696,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_9692])).

cnf(c_46,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_47,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9795,plain,
    ( v1_funct_1(X2_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9696,c_37,c_40,c_46,c_47])).

cnf(c_9796,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_9795])).

cnf(c_9809,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_9796])).

cnf(c_10373,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9809,c_38,c_43,c_44])).

cnf(c_10382,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_10373])).

cnf(c_10387,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10382,c_39])).

cnf(c_24993,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24992,c_10387])).

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
    inference(cnf_transformation,[],[f95])).

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

cnf(c_833,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_189])).

cnf(c_1364,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_1539,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X0_54,X4_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X0_54,X4_54))
    | k2_partfun1(k4_subset_1(X3_54,X0_54,X4_54),X1_54,k1_tmap_1(X3_54,X1_54,X0_54,X4_54,X2_54,X5_54),X0_54) = X2_54
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1364,c_1345])).

cnf(c_5619,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2885,c_1539])).

cnf(c_14728,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5619,c_37,c_38,c_43,c_44,c_45])).

cnf(c_14729,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_14728])).

cnf(c_14750,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_54,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_14729])).

cnf(c_14847,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_54,k1_xboole_0)
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14750,c_830])).

cnf(c_14848,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0_54,k1_xboole_0)
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14847,c_2364])).

cnf(c_14849,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14848,c_830,c_3300])).

cnf(c_15732,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14849,c_39,c_40,c_41])).

cnf(c_15733,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_54,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_15732])).

cnf(c_15743,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2880,c_15733])).

cnf(c_15744,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15743,c_3299])).

cnf(c_15745,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15744])).

cnf(c_15746,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15745,c_10387])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_846,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2583,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2364,c_846])).

cnf(c_2584,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2583,c_830])).

cnf(c_2978,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2584,c_2880,c_2885])).

cnf(c_3678,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3299,c_2978])).

cnf(c_5013,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3678,c_3300])).

cnf(c_5014,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_5013])).

cnf(c_10391,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_10387,c_5014])).

cnf(c_10392,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_10391,c_10387])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24993,c_15746,c_10392,c_48,c_47,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n025.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:04:50 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 7.61/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/1.47  
% 7.61/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.47  
% 7.61/1.47  ------  iProver source info
% 7.61/1.47  
% 7.61/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.47  git: non_committed_changes: false
% 7.61/1.47  git: last_make_outside_of_git: false
% 7.61/1.47  
% 7.61/1.47  ------ 
% 7.61/1.47  ------ Parsing...
% 7.61/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.47  
% 7.61/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.61/1.47  
% 7.61/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.47  
% 7.61/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.47  ------ Proving...
% 7.61/1.47  ------ Problem Properties 
% 7.61/1.47  
% 7.61/1.47  
% 7.61/1.47  clauses                                 29
% 7.61/1.47  conjectures                             13
% 7.61/1.47  EPR                                     8
% 7.61/1.47  Horn                                    22
% 7.61/1.47  unary                                   15
% 7.61/1.47  binary                                  2
% 7.61/1.47  lits                                    123
% 7.61/1.47  lits eq                                 19
% 7.61/1.47  fd_pure                                 0
% 7.61/1.47  fd_pseudo                               0
% 7.61/1.47  fd_cond                                 0
% 7.61/1.47  fd_pseudo_cond                          1
% 7.61/1.47  AC symbols                              0
% 7.61/1.47  
% 7.61/1.47  ------ Input Options Time Limit: Unbounded
% 7.61/1.47  
% 7.61/1.47  
% 7.61/1.47  ------ 
% 7.61/1.47  Current options:
% 7.61/1.47  ------ 
% 7.61/1.47  
% 7.61/1.47  
% 7.61/1.47  
% 7.61/1.47  
% 7.61/1.47  ------ Proving...
% 7.61/1.47  
% 7.61/1.47  
% 7.61/1.47  % SZS status Theorem for theBenchmark.p
% 7.61/1.47  
% 7.61/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.47  
% 7.61/1.47  fof(f16,conjecture,(
% 7.61/1.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f17,negated_conjecture,(
% 7.61/1.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.61/1.47    inference(negated_conjecture,[],[f16])).
% 7.61/1.47  
% 7.61/1.47  fof(f36,plain,(
% 7.61/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.61/1.47    inference(ennf_transformation,[],[f17])).
% 7.61/1.47  
% 7.61/1.47  fof(f37,plain,(
% 7.61/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.61/1.47    inference(flattening,[],[f36])).
% 7.61/1.47  
% 7.61/1.47  fof(f48,plain,(
% 7.61/1.47    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.61/1.47    introduced(choice_axiom,[])).
% 7.61/1.47  
% 7.61/1.47  fof(f47,plain,(
% 7.61/1.47    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.61/1.47    introduced(choice_axiom,[])).
% 7.61/1.47  
% 7.61/1.47  fof(f46,plain,(
% 7.61/1.47    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.61/1.47    introduced(choice_axiom,[])).
% 7.61/1.47  
% 7.61/1.47  fof(f45,plain,(
% 7.61/1.47    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.61/1.47    introduced(choice_axiom,[])).
% 7.61/1.47  
% 7.61/1.47  fof(f44,plain,(
% 7.61/1.47    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.61/1.47    introduced(choice_axiom,[])).
% 7.61/1.47  
% 7.61/1.47  fof(f43,plain,(
% 7.61/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.61/1.47    introduced(choice_axiom,[])).
% 7.61/1.47  
% 7.61/1.47  fof(f49,plain,(
% 7.61/1.47    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.61/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f48,f47,f46,f45,f44,f43])).
% 7.61/1.47  
% 7.61/1.47  fof(f85,plain,(
% 7.61/1.47    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f13,axiom,(
% 7.61/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f30,plain,(
% 7.61/1.47    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.61/1.47    inference(ennf_transformation,[],[f13])).
% 7.61/1.47  
% 7.61/1.47  fof(f31,plain,(
% 7.61/1.47    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.61/1.47    inference(flattening,[],[f30])).
% 7.61/1.47  
% 7.61/1.47  fof(f66,plain,(
% 7.61/1.47    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f31])).
% 7.61/1.47  
% 7.61/1.47  fof(f83,plain,(
% 7.61/1.47    v1_funct_1(sK5)),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f78,plain,(
% 7.61/1.47    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f4,axiom,(
% 7.61/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f19,plain,(
% 7.61/1.47    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.61/1.47    inference(ennf_transformation,[],[f4])).
% 7.61/1.47  
% 7.61/1.47  fof(f54,plain,(
% 7.61/1.47    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.61/1.47    inference(cnf_transformation,[],[f19])).
% 7.61/1.47  
% 7.61/1.47  fof(f6,axiom,(
% 7.61/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f56,plain,(
% 7.61/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.61/1.47    inference(cnf_transformation,[],[f6])).
% 7.61/1.47  
% 7.61/1.47  fof(f90,plain,(
% 7.61/1.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.61/1.47    inference(definition_unfolding,[],[f54,f56])).
% 7.61/1.47  
% 7.61/1.47  fof(f82,plain,(
% 7.61/1.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f80,plain,(
% 7.61/1.47    v1_funct_1(sK4)),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f14,axiom,(
% 7.61/1.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f32,plain,(
% 7.61/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.61/1.47    inference(ennf_transformation,[],[f14])).
% 7.61/1.47  
% 7.61/1.47  fof(f33,plain,(
% 7.61/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.61/1.47    inference(flattening,[],[f32])).
% 7.61/1.47  
% 7.61/1.47  fof(f41,plain,(
% 7.61/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.61/1.47    inference(nnf_transformation,[],[f33])).
% 7.61/1.47  
% 7.61/1.47  fof(f42,plain,(
% 7.61/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.61/1.47    inference(flattening,[],[f41])).
% 7.61/1.47  
% 7.61/1.47  fof(f68,plain,(
% 7.61/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f42])).
% 7.61/1.47  
% 7.61/1.47  fof(f94,plain,(
% 7.61/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.47    inference(equality_resolution,[],[f68])).
% 7.61/1.47  
% 7.61/1.47  fof(f15,axiom,(
% 7.61/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f34,plain,(
% 7.61/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.61/1.47    inference(ennf_transformation,[],[f15])).
% 7.61/1.47  
% 7.61/1.47  fof(f35,plain,(
% 7.61/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.61/1.47    inference(flattening,[],[f34])).
% 7.61/1.47  
% 7.61/1.47  fof(f70,plain,(
% 7.61/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f35])).
% 7.61/1.47  
% 7.61/1.47  fof(f71,plain,(
% 7.61/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f35])).
% 7.61/1.47  
% 7.61/1.47  fof(f72,plain,(
% 7.61/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f35])).
% 7.61/1.47  
% 7.61/1.47  fof(f5,axiom,(
% 7.61/1.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f20,plain,(
% 7.61/1.47    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.61/1.47    inference(ennf_transformation,[],[f5])).
% 7.61/1.47  
% 7.61/1.47  fof(f55,plain,(
% 7.61/1.47    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f20])).
% 7.61/1.47  
% 7.61/1.47  fof(f74,plain,(
% 7.61/1.47    ~v1_xboole_0(sK1)),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f75,plain,(
% 7.61/1.47    ~v1_xboole_0(sK2)),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f81,plain,(
% 7.61/1.47    v1_funct_2(sK4,sK2,sK1)),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f1,axiom,(
% 7.61/1.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f38,plain,(
% 7.61/1.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.61/1.47    inference(nnf_transformation,[],[f1])).
% 7.61/1.47  
% 7.61/1.47  fof(f50,plain,(
% 7.61/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f38])).
% 7.61/1.47  
% 7.61/1.47  fof(f88,plain,(
% 7.61/1.47    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.61/1.47    inference(definition_unfolding,[],[f50,f56])).
% 7.61/1.47  
% 7.61/1.47  fof(f8,axiom,(
% 7.61/1.47    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f22,plain,(
% 7.61/1.47    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.61/1.47    inference(ennf_transformation,[],[f8])).
% 7.61/1.47  
% 7.61/1.47  fof(f23,plain,(
% 7.61/1.47    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.61/1.47    inference(flattening,[],[f22])).
% 7.61/1.47  
% 7.61/1.47  fof(f39,plain,(
% 7.61/1.47    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.61/1.47    inference(nnf_transformation,[],[f23])).
% 7.61/1.47  
% 7.61/1.47  fof(f58,plain,(
% 7.61/1.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f39])).
% 7.61/1.47  
% 7.61/1.47  fof(f79,plain,(
% 7.61/1.47    r1_subset_1(sK2,sK3)),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f77,plain,(
% 7.61/1.47    ~v1_xboole_0(sK3)),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f9,axiom,(
% 7.61/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f24,plain,(
% 7.61/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.61/1.47    inference(ennf_transformation,[],[f9])).
% 7.61/1.47  
% 7.61/1.47  fof(f60,plain,(
% 7.61/1.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.61/1.47    inference(cnf_transformation,[],[f24])).
% 7.61/1.47  
% 7.61/1.47  fof(f3,axiom,(
% 7.61/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f53,plain,(
% 7.61/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f3])).
% 7.61/1.47  
% 7.61/1.47  fof(f2,axiom,(
% 7.61/1.47    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f52,plain,(
% 7.61/1.47    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.61/1.47    inference(cnf_transformation,[],[f2])).
% 7.61/1.47  
% 7.61/1.47  fof(f89,plain,(
% 7.61/1.47    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 7.61/1.47    inference(definition_unfolding,[],[f52,f56])).
% 7.61/1.47  
% 7.61/1.47  fof(f51,plain,(
% 7.61/1.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.61/1.47    inference(cnf_transformation,[],[f38])).
% 7.61/1.47  
% 7.61/1.47  fof(f87,plain,(
% 7.61/1.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.61/1.47    inference(definition_unfolding,[],[f51,f56])).
% 7.61/1.47  
% 7.61/1.47  fof(f7,axiom,(
% 7.61/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.61/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.47  
% 7.61/1.47  fof(f21,plain,(
% 7.61/1.47    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.61/1.47    inference(ennf_transformation,[],[f7])).
% 7.61/1.47  
% 7.61/1.47  fof(f57,plain,(
% 7.61/1.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f21])).
% 7.61/1.47  
% 7.61/1.47  fof(f76,plain,(
% 7.61/1.47    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f84,plain,(
% 7.61/1.47    v1_funct_2(sK5,sK3,sK1)),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  fof(f67,plain,(
% 7.61/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.47    inference(cnf_transformation,[],[f42])).
% 7.61/1.47  
% 7.61/1.47  fof(f95,plain,(
% 7.61/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.61/1.47    inference(equality_resolution,[],[f67])).
% 7.61/1.47  
% 7.61/1.47  fof(f86,plain,(
% 7.61/1.47    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.61/1.47    inference(cnf_transformation,[],[f49])).
% 7.61/1.47  
% 7.61/1.47  cnf(c_23,negated_conjecture,
% 7.61/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.61/1.47      inference(cnf_transformation,[],[f85]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_845,negated_conjecture,
% 7.61/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_23]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1352,plain,
% 7.61/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_15,plain,
% 7.61/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.61/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_851,plain,
% 7.61/1.47      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.61/1.47      | ~ v1_funct_1(X0_54)
% 7.61/1.47      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_15]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1347,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X2_54) != iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2483,plain,
% 7.61/1.47      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1352,c_1347]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_25,negated_conjecture,
% 7.61/1.47      ( v1_funct_1(sK5) ),
% 7.61/1.47      inference(cnf_transformation,[],[f83]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1798,plain,
% 7.61/1.47      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.61/1.47      | ~ v1_funct_1(sK5)
% 7.61/1.47      | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
% 7.61/1.47      inference(instantiation,[status(thm)],[c_851]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2014,plain,
% 7.61/1.47      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.61/1.47      | ~ v1_funct_1(sK5)
% 7.61/1.47      | k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.61/1.47      inference(instantiation,[status(thm)],[c_1798]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2880,plain,
% 7.61/1.47      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_2483,c_25,c_23,c_2014]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_30,negated_conjecture,
% 7.61/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.61/1.47      inference(cnf_transformation,[],[f78]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_839,negated_conjecture,
% 7.61/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_30]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1358,plain,
% 7.61/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_4,plain,
% 7.61/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.61/1.47      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.61/1.47      inference(cnf_transformation,[],[f90]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_854,plain,
% 7.61/1.47      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.61/1.47      | k9_subset_1(X1_54,X2_54,X0_54) = k1_setfam_1(k2_tarski(X2_54,X0_54)) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_4]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1344,plain,
% 7.61/1.47      ( k9_subset_1(X0_54,X1_54,X2_54) = k1_setfam_1(k2_tarski(X1_54,X2_54))
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2364,plain,
% 7.61/1.47      ( k9_subset_1(sK0,X0_54,sK3) = k1_setfam_1(k2_tarski(X0_54,sK3)) ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1358,c_1344]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_26,negated_conjecture,
% 7.61/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.61/1.47      inference(cnf_transformation,[],[f82]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_842,negated_conjecture,
% 7.61/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_26]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1355,plain,
% 7.61/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2484,plain,
% 7.61/1.47      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 7.61/1.47      | v1_funct_1(sK4) != iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1355,c_1347]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_28,negated_conjecture,
% 7.61/1.47      ( v1_funct_1(sK4) ),
% 7.61/1.47      inference(cnf_transformation,[],[f80]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1803,plain,
% 7.61/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.61/1.47      | ~ v1_funct_1(sK4)
% 7.61/1.47      | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
% 7.61/1.47      inference(instantiation,[status(thm)],[c_851]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2019,plain,
% 7.61/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.61/1.47      | ~ v1_funct_1(sK4)
% 7.61/1.47      | k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.61/1.47      inference(instantiation,[status(thm)],[c_1803]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2885,plain,
% 7.61/1.47      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_2484,c_28,c_26,c_2019]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_17,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_1(X3)
% 7.61/1.47      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X1)
% 7.61/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.61/1.47      inference(cnf_transformation,[],[f94]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_21,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_1(X3)
% 7.61/1.47      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X1) ),
% 7.61/1.47      inference(cnf_transformation,[],[f70]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_20,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_1(X3)
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X1) ),
% 7.61/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_19,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_1(X3)
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X1) ),
% 7.61/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_195,plain,
% 7.61/1.47      ( ~ v1_funct_1(X3)
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X1)
% 7.61/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_17,c_21,c_20,c_19]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_196,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_1(X3)
% 7.61/1.47      | v1_xboole_0(X1)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.61/1.47      inference(renaming,[status(thm)],[c_195]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_832,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.61/1.47      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.61/1.47      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.61/1.47      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.61/1.47      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.61/1.47      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.61/1.47      | ~ v1_funct_1(X0_54)
% 7.61/1.47      | ~ v1_funct_1(X3_54)
% 7.61/1.47      | v1_xboole_0(X2_54)
% 7.61/1.47      | v1_xboole_0(X1_54)
% 7.61/1.47      | v1_xboole_0(X4_54)
% 7.61/1.47      | v1_xboole_0(X5_54)
% 7.61/1.47      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_196]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1365,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 7.61/1.47      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X3_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_5,plain,
% 7.61/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.61/1.47      | ~ v1_xboole_0(X1)
% 7.61/1.47      | v1_xboole_0(X0) ),
% 7.61/1.47      inference(cnf_transformation,[],[f55]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_853,plain,
% 7.61/1.47      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.61/1.47      | ~ v1_xboole_0(X1_54)
% 7.61/1.47      | v1_xboole_0(X0_54) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_5]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1345,plain,
% 7.61/1.47      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1567,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X0_54,X4_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X0_54,X4_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X3_54,X0_54,X4_54),X1_54,k1_tmap_1(X3_54,X1_54,X0_54,X4_54,X2_54,X5_54),X4_54) = X5_54
% 7.61/1.47      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X4_54) = iProver_top ),
% 7.61/1.47      inference(forward_subsumption_resolution,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_1365,c_1345]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_6815,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
% 7.61/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.61/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | v1_funct_1(X1_54) != iProver_top
% 7.61/1.47      | v1_funct_1(sK4) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.61/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_2885,c_1567]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_34,negated_conjecture,
% 7.61/1.47      ( ~ v1_xboole_0(sK1) ),
% 7.61/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_37,plain,
% 7.61/1.47      ( v1_xboole_0(sK1) != iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_33,negated_conjecture,
% 7.61/1.47      ( ~ v1_xboole_0(sK2) ),
% 7.61/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_38,plain,
% 7.61/1.47      ( v1_xboole_0(sK2) != iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_43,plain,
% 7.61/1.47      ( v1_funct_1(sK4) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_27,negated_conjecture,
% 7.61/1.47      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.61/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_44,plain,
% 7.61/1.47      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_45,plain,
% 7.61/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24580,plain,
% 7.61/1.47      ( v1_funct_1(X1_54) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.61/1.47      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
% 7.61/1.47      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_6815,c_37,c_38,c_43,c_44,c_45]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24581,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
% 7.61/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | v1_funct_1(X1_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.61/1.47      inference(renaming,[status(thm)],[c_24580]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24602,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
% 7.61/1.47      | k2_partfun1(sK3,sK1,X0_54,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_2364,c_24581]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1,plain,
% 7.61/1.47      ( ~ r1_xboole_0(X0,X1)
% 7.61/1.47      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.61/1.47      inference(cnf_transformation,[],[f88]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_252,plain,
% 7.61/1.47      ( ~ r1_xboole_0(X0,X1)
% 7.61/1.47      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.61/1.47      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_8,plain,
% 7.61/1.47      ( ~ r1_subset_1(X0,X1)
% 7.61/1.47      | r1_xboole_0(X0,X1)
% 7.61/1.47      | v1_xboole_0(X0)
% 7.61/1.47      | v1_xboole_0(X1) ),
% 7.61/1.47      inference(cnf_transformation,[],[f58]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_29,negated_conjecture,
% 7.61/1.47      ( r1_subset_1(sK2,sK3) ),
% 7.61/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_506,plain,
% 7.61/1.47      ( r1_xboole_0(X0,X1)
% 7.61/1.47      | v1_xboole_0(X0)
% 7.61/1.47      | v1_xboole_0(X1)
% 7.61/1.47      | sK3 != X1
% 7.61/1.47      | sK2 != X0 ),
% 7.61/1.47      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_507,plain,
% 7.61/1.47      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.61/1.47      inference(unflattening,[status(thm)],[c_506]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_31,negated_conjecture,
% 7.61/1.47      ( ~ v1_xboole_0(sK3) ),
% 7.61/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_509,plain,
% 7.61/1.47      ( r1_xboole_0(sK2,sK3) ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_507,c_33,c_31]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_535,plain,
% 7.61/1.47      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 7.61/1.47      | sK3 != X1
% 7.61/1.47      | sK2 != X0 ),
% 7.61/1.47      inference(resolution_lifted,[status(thm)],[c_252,c_509]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_536,plain,
% 7.61/1.47      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.61/1.47      inference(unflattening,[status(thm)],[c_535]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_830,plain,
% 7.61/1.47      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_536]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24699,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
% 7.61/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_54,k1_xboole_0)
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(light_normalisation,[status(thm)],[c_24602,c_830]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24700,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
% 7.61/1.47      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0_54,k1_xboole_0)
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_24699,c_2364]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_9,plain,
% 7.61/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | v1_relat_1(X0) ),
% 7.61/1.47      inference(cnf_transformation,[],[f60]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_852,plain,
% 7.61/1.47      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.61/1.47      | v1_relat_1(X0_54) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_9]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1346,plain,
% 7.61/1.47      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.61/1.47      | v1_relat_1(X0_54) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2283,plain,
% 7.61/1.47      ( v1_relat_1(sK4) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1355,c_1346]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_3,plain,
% 7.61/1.47      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.61/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_855,plain,
% 7.61/1.47      ( k2_tarski(X0_54,X1_54) = k2_tarski(X1_54,X0_54) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_3]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2,plain,
% 7.61/1.47      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.61/1.47      inference(cnf_transformation,[],[f89]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_856,plain,
% 7.61/1.47      ( k1_setfam_1(k2_tarski(X0_54,k1_xboole_0)) = k1_xboole_0 ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_2]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1955,plain,
% 7.61/1.47      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0_54)) = k1_xboole_0 ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_855,c_856]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_0,plain,
% 7.61/1.47      ( r1_xboole_0(X0,X1)
% 7.61/1.47      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 7.61/1.47      inference(cnf_transformation,[],[f87]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_250,plain,
% 7.61/1.47      ( r1_xboole_0(X0,X1)
% 7.61/1.47      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 7.61/1.47      inference(prop_impl,[status(thm)],[c_0]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_6,plain,
% 7.61/1.47      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.61/1.47      | ~ v1_relat_1(X1)
% 7.61/1.47      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.61/1.47      inference(cnf_transformation,[],[f57]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_520,plain,
% 7.61/1.47      ( ~ v1_relat_1(X0)
% 7.61/1.47      | X1 != X2
% 7.61/1.47      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.61/1.47      | k1_relat_1(X0) != X3
% 7.61/1.47      | k1_setfam_1(k2_tarski(X2,X3)) != k1_xboole_0 ),
% 7.61/1.47      inference(resolution_lifted,[status(thm)],[c_250,c_6]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_521,plain,
% 7.61/1.47      ( ~ v1_relat_1(X0)
% 7.61/1.47      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.61/1.47      | k1_setfam_1(k2_tarski(X1,k1_relat_1(X0))) != k1_xboole_0 ),
% 7.61/1.47      inference(unflattening,[status(thm)],[c_520]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_831,plain,
% 7.61/1.47      ( ~ v1_relat_1(X0_54)
% 7.61/1.47      | k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 7.61/1.47      | k1_setfam_1(k2_tarski(X1_54,k1_relat_1(X0_54))) != k1_xboole_0 ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_521]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1366,plain,
% 7.61/1.47      ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 7.61/1.47      | k1_setfam_1(k2_tarski(X1_54,k1_relat_1(X0_54))) != k1_xboole_0
% 7.61/1.47      | v1_relat_1(X0_54) != iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2986,plain,
% 7.61/1.47      ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
% 7.61/1.47      | v1_relat_1(X0_54) != iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1955,c_1366]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_3300,plain,
% 7.61/1.47      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_2283,c_2986]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24701,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
% 7.61/1.47      | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(light_normalisation,[status(thm)],[c_24700,c_830,c_3300]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_32,negated_conjecture,
% 7.61/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.61/1.47      inference(cnf_transformation,[],[f76]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_39,plain,
% 7.61/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_40,plain,
% 7.61/1.47      ( v1_xboole_0(sK3) != iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_41,plain,
% 7.61/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24979,plain,
% 7.61/1.47      ( v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54 ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_24701,c_39,c_40,c_41]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24980,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK3) = X0_54
% 7.61/1.47      | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top ),
% 7.61/1.47      inference(renaming,[status(thm)],[c_24979]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24990,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.61/1.47      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_2880,c_24980]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2282,plain,
% 7.61/1.47      ( v1_relat_1(sK5) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1352,c_1346]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_3299,plain,
% 7.61/1.47      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_2282,c_2986]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24991,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.61/1.47      | k1_xboole_0 != k1_xboole_0
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(light_normalisation,[status(thm)],[c_24990,c_3299]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24992,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(equality_resolution_simp,[status(thm)],[c_24991]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_849,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.61/1.47      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.61/1.47      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.61/1.47      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.61/1.47      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.61/1.47      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.61/1.47      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
% 7.61/1.47      | ~ v1_funct_1(X0_54)
% 7.61/1.47      | ~ v1_funct_1(X3_54)
% 7.61/1.47      | v1_xboole_0(X2_54)
% 7.61/1.47      | v1_xboole_0(X1_54)
% 7.61/1.47      | v1_xboole_0(X4_54)
% 7.61/1.47      | v1_xboole_0(X5_54) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_19]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1349,plain,
% 7.61/1.47      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X3_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X5_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1512,plain,
% 7.61/1.47      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X3_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top ),
% 7.61/1.47      inference(forward_subsumption_resolution,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_1349,c_1345]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_4868,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.61/1.47      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X4_54) != iProver_top
% 7.61/1.47      | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
% 7.61/1.47      | v1_xboole_0(X3_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X2_54) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1512,c_1347]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_847,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.61/1.47      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.61/1.47      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.61/1.47      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.61/1.47      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.61/1.47      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.61/1.47      | ~ v1_funct_1(X0_54)
% 7.61/1.47      | ~ v1_funct_1(X3_54)
% 7.61/1.47      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
% 7.61/1.47      | v1_xboole_0(X2_54)
% 7.61/1.47      | v1_xboole_0(X1_54)
% 7.61/1.47      | v1_xboole_0(X4_54)
% 7.61/1.47      | v1_xboole_0(X5_54) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_21]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1351,plain,
% 7.61/1.47      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X3_54) != iProver_top
% 7.61/1.47      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
% 7.61/1.47      | v1_xboole_0(X5_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1460,plain,
% 7.61/1.47      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X3_54) != iProver_top
% 7.61/1.47      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
% 7.61/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top ),
% 7.61/1.47      inference(forward_subsumption_resolution,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_1351,c_1345]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_9692,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.61/1.47      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X4_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X3_54) = iProver_top ),
% 7.61/1.47      inference(forward_subsumption_resolution,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_4868,c_1460]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_9696,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.61/1.47      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1352,c_9692]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_46,plain,
% 7.61/1.47      ( v1_funct_1(sK5) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24,negated_conjecture,
% 7.61/1.47      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.61/1.47      inference(cnf_transformation,[],[f84]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_47,plain,
% 7.61/1.47      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_9795,plain,
% 7.61/1.47      ( v1_funct_1(X2_54) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.61/1.47      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_9696,c_37,c_40,c_46,c_47]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_9796,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.61/1.47      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top ),
% 7.61/1.47      inference(renaming,[status(thm)],[c_9795]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_9809,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 7.61/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | v1_funct_1(sK4) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1355,c_9796]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_10373,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_9809,c_38,c_43,c_44]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_10382,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54)
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_1358,c_10373]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_10387,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_10382,c_39]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_24993,plain,
% 7.61/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_24992,c_10387]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_18,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_1(X3)
% 7.61/1.47      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X1)
% 7.61/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.61/1.47      inference(cnf_transformation,[],[f95]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_188,plain,
% 7.61/1.47      ( ~ v1_funct_1(X3)
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X1)
% 7.61/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_18,c_21,c_20,c_19]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_189,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.61/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.61/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.61/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.61/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.61/1.47      | ~ v1_funct_1(X0)
% 7.61/1.47      | ~ v1_funct_1(X3)
% 7.61/1.47      | v1_xboole_0(X1)
% 7.61/1.47      | v1_xboole_0(X2)
% 7.61/1.47      | v1_xboole_0(X4)
% 7.61/1.47      | v1_xboole_0(X5)
% 7.61/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.61/1.47      inference(renaming,[status(thm)],[c_188]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_833,plain,
% 7.61/1.47      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.61/1.47      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.61/1.47      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.61/1.47      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.61/1.47      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.61/1.47      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.61/1.47      | ~ v1_funct_1(X0_54)
% 7.61/1.47      | ~ v1_funct_1(X3_54)
% 7.61/1.47      | v1_xboole_0(X2_54)
% 7.61/1.47      | v1_xboole_0(X1_54)
% 7.61/1.47      | v1_xboole_0(X4_54)
% 7.61/1.47      | v1_xboole_0(X5_54)
% 7.61/1.47      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_189]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1364,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 7.61/1.47      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X3_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_1539,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X0_54,X4_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X0_54,X4_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X3_54,X0_54,X4_54),X1_54,k1_tmap_1(X3_54,X1_54,X0_54,X4_54,X2_54,X5_54),X0_54) = X2_54
% 7.61/1.47      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.61/1.47      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.61/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.61/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.61/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(X4_54) = iProver_top ),
% 7.61/1.47      inference(forward_subsumption_resolution,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_1364,c_1345]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_5619,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
% 7.61/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.61/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | v1_funct_1(X1_54) != iProver_top
% 7.61/1.47      | v1_funct_1(sK4) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.61/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.61/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_2885,c_1539]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_14728,plain,
% 7.61/1.47      ( v1_funct_1(X1_54) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.61/1.47      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
% 7.61/1.47      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_5619,c_37,c_38,c_43,c_44,c_45]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_14729,plain,
% 7.61/1.47      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.61/1.47      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
% 7.61/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.61/1.47      | v1_funct_1(X1_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.61/1.47      inference(renaming,[status(thm)],[c_14728]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_14750,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
% 7.61/1.47      | k2_partfun1(sK3,sK1,X0_54,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_2364,c_14729]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_14847,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
% 7.61/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_54,k1_xboole_0)
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(light_normalisation,[status(thm)],[c_14750,c_830]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_14848,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
% 7.61/1.47      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0_54,k1_xboole_0)
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_14847,c_2364]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_14849,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
% 7.61/1.47      | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.61/1.47      inference(light_normalisation,[status(thm)],[c_14848,c_830,c_3300]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_15732,plain,
% 7.61/1.47      ( v1_funct_1(X0_54) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4 ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_14849,c_39,c_40,c_41]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_15733,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_54),sK2) = sK4
% 7.61/1.47      | k2_partfun1(sK3,sK1,X0_54,k1_xboole_0) != k1_xboole_0
% 7.61/1.47      | v1_funct_2(X0_54,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(X0_54) != iProver_top ),
% 7.61/1.47      inference(renaming,[status(thm)],[c_15732]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_15743,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.61/1.47      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(superposition,[status(thm)],[c_2880,c_15733]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_15744,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.61/1.47      | k1_xboole_0 != k1_xboole_0
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(light_normalisation,[status(thm)],[c_15743,c_3299]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_15745,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(equality_resolution_simp,[status(thm)],[c_15744]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_15746,plain,
% 7.61/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.61/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.61/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.61/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_15745,c_10387]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_22,negated_conjecture,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.47      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.61/1.47      inference(cnf_transformation,[],[f86]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_846,negated_conjecture,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.47      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.61/1.47      inference(subtyping,[status(esa)],[c_22]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2583,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.47      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_2364,c_846]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2584,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.47      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.61/1.47      inference(light_normalisation,[status(thm)],[c_2583,c_830]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_2978,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.47      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_2584,c_2880,c_2885]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_3678,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.47      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_3299,c_2978]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_5013,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.61/1.47      inference(global_propositional_subsumption,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_3678,c_3300]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_5014,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.61/1.47      inference(renaming,[status(thm)],[c_5013]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_10391,plain,
% 7.61/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.61/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_10387,c_5014]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_10392,plain,
% 7.61/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.61/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.61/1.47      inference(demodulation,[status(thm)],[c_10391,c_10387]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(c_48,plain,
% 7.61/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.61/1.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.61/1.47  
% 7.61/1.47  cnf(contradiction,plain,
% 7.61/1.47      ( $false ),
% 7.61/1.47      inference(minisat,
% 7.61/1.47                [status(thm)],
% 7.61/1.47                [c_24993,c_15746,c_10392,c_48,c_47,c_46]) ).
% 7.61/1.47  
% 7.61/1.47  
% 7.61/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.47  
% 7.61/1.47  ------                               Statistics
% 7.61/1.47  
% 7.61/1.47  ------ Selected
% 7.61/1.47  
% 7.61/1.47  total_time:                             0.99
% 7.61/1.47  
%------------------------------------------------------------------------------
