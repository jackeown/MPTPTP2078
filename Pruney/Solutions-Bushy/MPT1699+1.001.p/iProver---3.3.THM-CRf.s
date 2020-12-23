%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1699+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:12 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  196 (2790 expanded)
%              Number of clauses        :  140 ( 555 expanded)
%              Number of leaves         :   18 (1219 expanded)
%              Depth                    :   26
%              Number of atoms          : 1586 (39091 expanded)
%              Number of equality atoms :  468 (4154 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal clause size      :   28 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f6,conjecture,(
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
                           => r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                             => r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
                          & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
                          & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
          & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),k1_tmap_1(X0,X1,X3,X2,sK5,X4))
        & k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) = k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK5,X3,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
              & v1_funct_2(X5,X3,X1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          & v1_funct_2(X4,X2,X1)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),k1_tmap_1(X0,X1,X3,X2,X5,sK4))
            & k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK4,X2,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
                  & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                  & v1_funct_2(X5,X3,X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(X4,X2,X1)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(X0))
          & ~ v1_xboole_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_funct_2(k4_subset_1(X0,X2,sK3),X1,k4_subset_1(X0,sK3,X2),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),k1_tmap_1(X0,X1,sK3,X2,X5,X4))
                & k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) = k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
                & v1_funct_2(X5,sK3,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
                      & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X5,X3,X1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                  & v1_funct_2(X4,X2,X1)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(X0))
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_funct_2(k4_subset_1(X0,sK2,X3),X1,k4_subset_1(X0,X3,sK2),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),k1_tmap_1(X0,X1,X3,sK2,X5,X4))
                    & k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
                & v1_funct_2(X4,sK2,X1)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
                          & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),sK1,k4_subset_1(X0,X3,X2),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),k1_tmap_1(X0,sK1,X3,X2,X5,X4))
                        & k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                        & v1_funct_2(X5,X3,sK1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                    & v1_funct_2(X4,X2,sK1)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
                            & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
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
                          ( ~ r1_funct_2(k4_subset_1(sK0,X2,X3),X1,k4_subset_1(sK0,X3,X2),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),k1_tmap_1(sK0,X1,X3,X2,X5,X4))
                          & k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK3,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    & k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK5,sK3,sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f27,f26,f25,f24,f23,f22])).

fof(f51,plain,(
    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
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
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
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
    inference(equality_resolution,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4
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
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( k1_tmap_1(X0,X1,X2,X3,X4,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3)) = X6
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),X3,X1)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f54,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k1_tmap_1(X0,X1,X2,X3,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3)) = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),X3,X1)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),X2,X1)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ~ r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK3,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_224,plain,
    ( r1_funct_2(X0_45,X1_45,X2_45,X3_45,X4_45,X4_45)
    | ~ v1_funct_2(X4_45,X0_45,X1_45)
    | ~ v1_funct_2(X4_45,X2_45,X3_45)
    | ~ m1_subset_1(X4_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(X4_45,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X3_45)
    | ~ v1_funct_1(X4_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_635,plain,
    ( r1_funct_2(X0_45,X1_45,X2_45,X3_45,X4_45,X4_45) = iProver_top
    | v1_funct_2(X4_45,X0_45,X1_45) != iProver_top
    | v1_funct_2(X4_45,X2_45,X3_45) != iProver_top
    | m1_subset_1(X4_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | m1_subset_1(X4_45,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45))) != iProver_top
    | v1_xboole_0(X3_45) = iProver_top
    | v1_xboole_0(X1_45) = iProver_top
    | v1_funct_1(X4_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_11,negated_conjecture,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_221,negated_conjecture,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_185,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_7,c_6,c_5])).

cnf(c_186,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_207,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(X3_45,X4_45,X2_45)
    | ~ m1_subset_1(X4_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(X4_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X5_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X3_45)
    | k2_partfun1(X1_45,X2_45,X0_45,k9_subset_1(X5_45,X4_45,X1_45)) != k2_partfun1(X4_45,X2_45,X3_45,k9_subset_1(X5_45,X4_45,X1_45))
    | k2_partfun1(k4_subset_1(X5_45,X4_45,X1_45),X2_45,k1_tmap_1(X5_45,X2_45,X4_45,X1_45,X3_45,X0_45),X4_45) = X3_45 ),
    inference(subtyping,[status(esa)],[c_186])).

cnf(c_651,plain,
    ( k2_partfun1(X0_45,X1_45,X2_45,k9_subset_1(X3_45,X4_45,X0_45)) != k2_partfun1(X4_45,X1_45,X5_45,k9_subset_1(X3_45,X4_45,X0_45))
    | k2_partfun1(k4_subset_1(X3_45,X4_45,X0_45),X1_45,k1_tmap_1(X3_45,X1_45,X4_45,X0_45,X5_45,X2_45),X4_45) = X5_45
    | v1_funct_2(X2_45,X0_45,X1_45) != iProver_top
    | v1_funct_2(X5_45,X4_45,X1_45) != iProver_top
    | m1_subset_1(X4_45,k1_zfmisc_1(X3_45)) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(X3_45)) != iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | m1_subset_1(X5_45,k1_zfmisc_1(k2_zfmisc_1(X4_45,X1_45))) != iProver_top
    | v1_xboole_0(X3_45) = iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_xboole_0(X1_45) = iProver_top
    | v1_xboole_0(X4_45) = iProver_top
    | v1_funct_1(X2_45) != iProver_top
    | v1_funct_1(X5_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_7303,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_45,sK5),sK2) = X0_45
    | k2_partfun1(sK2,sK1,X0_45,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_45,sK2,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_221,c_651])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_24,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_25,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_26,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_28,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_33,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_34,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8348,plain,
    ( v1_funct_1(X0_45) != iProver_top
    | v1_funct_2(X0_45,sK2,sK1) != iProver_top
    | k2_partfun1(sK2,sK1,X0_45,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_45,sK5),sK2) = X0_45
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7303,c_24,c_25,c_26,c_27,c_28,c_29,c_33,c_34,c_35])).

cnf(c_8349,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_45,sK5),sK2) = X0_45
    | k2_partfun1(sK2,sK1,X0_45,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_45,sK2,sK1) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_8348])).

cnf(c_8359,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8349])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_234,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_232,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1369,plain,
    ( X0_45 != X1_45
    | X1_45 = X0_45 ),
    inference(resolution,[status(thm)],[c_234,c_232])).

cnf(c_1455,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_1369,c_221])).

cnf(c_1089,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(sK4,X3_45,X2_45)
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(X4_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X4_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X3_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X1_45,X2_45,X0_45,k9_subset_1(X4_45,X3_45,X1_45)) != k2_partfun1(X3_45,X2_45,sK4,k9_subset_1(X4_45,X3_45,X1_45))
    | k2_partfun1(k4_subset_1(X4_45,X3_45,X1_45),X2_45,k1_tmap_1(X4_45,X2_45,X3_45,X1_45,sK4,X0_45),X3_45) = sK4 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_1318,plain,
    ( ~ v1_funct_2(sK5,X0_45,X1_45)
    | ~ v1_funct_2(sK4,X2_45,X1_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X3_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_45,X1_45,sK5,k9_subset_1(X3_45,X2_45,X0_45)) != k2_partfun1(X2_45,X1_45,sK4,k9_subset_1(X3_45,X2_45,X0_45))
    | k2_partfun1(k4_subset_1(X3_45,X2_45,X0_45),X1_45,k1_tmap_1(X3_45,X1_45,X2_45,X0_45,sK4,sK5),X2_45) = sK4 ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_1633,plain,
    ( ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_45))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_45,sK1,sK5,k9_subset_1(X1_45,sK2,X0_45)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1_45,sK2,X0_45))
    | k2_partfun1(k4_subset_1(X1_45,sK2,X0_45),sK1,k1_tmap_1(X1_45,sK1,sK2,X0_45,sK4,sK5),sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_2018,plain,
    ( ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_45,sK1,sK5,k9_subset_1(sK0,sK2,X0_45)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0_45))
    | k2_partfun1(k4_subset_1(sK0,sK2,X0_45),sK1,k1_tmap_1(sK0,sK1,sK2,X0_45,sK4,sK5),sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_3405,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_9128,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8359,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_13,c_12,c_1455,c_3405])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_176,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_7,c_6,c_5])).

cnf(c_177,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_208,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(X3_45,X4_45,X2_45)
    | ~ m1_subset_1(X4_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(X4_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X5_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X3_45)
    | k2_partfun1(X1_45,X2_45,X0_45,k9_subset_1(X5_45,X4_45,X1_45)) != k2_partfun1(X4_45,X2_45,X3_45,k9_subset_1(X5_45,X4_45,X1_45))
    | k2_partfun1(k4_subset_1(X5_45,X4_45,X1_45),X2_45,k1_tmap_1(X5_45,X2_45,X4_45,X1_45,X3_45,X0_45),X1_45) = X0_45 ),
    inference(subtyping,[status(esa)],[c_177])).

cnf(c_650,plain,
    ( k2_partfun1(X0_45,X1_45,X2_45,k9_subset_1(X3_45,X4_45,X0_45)) != k2_partfun1(X4_45,X1_45,X5_45,k9_subset_1(X3_45,X4_45,X0_45))
    | k2_partfun1(k4_subset_1(X3_45,X4_45,X0_45),X1_45,k1_tmap_1(X3_45,X1_45,X4_45,X0_45,X5_45,X2_45),X0_45) = X2_45
    | v1_funct_2(X2_45,X0_45,X1_45) != iProver_top
    | v1_funct_2(X5_45,X4_45,X1_45) != iProver_top
    | m1_subset_1(X4_45,k1_zfmisc_1(X3_45)) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(X3_45)) != iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | m1_subset_1(X5_45,k1_zfmisc_1(k2_zfmisc_1(X4_45,X1_45))) != iProver_top
    | v1_xboole_0(X3_45) = iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_xboole_0(X1_45) = iProver_top
    | v1_xboole_0(X4_45) = iProver_top
    | v1_funct_1(X2_45) != iProver_top
    | v1_funct_1(X5_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_4609,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_45,sK5),sK3) = sK5
    | k2_partfun1(sK2,sK1,X0_45,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_45,sK2,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_221,c_650])).

cnf(c_5302,plain,
    ( v1_funct_1(X0_45) != iProver_top
    | v1_funct_2(X0_45,sK2,sK1) != iProver_top
    | k2_partfun1(sK2,sK1,X0_45,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_45,sK5),sK3) = sK5
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4609,c_24,c_25,c_26,c_27,c_28,c_29,c_33,c_34,c_35])).

cnf(c_5303,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_45,sK5),sK3) = sK5
    | k2_partfun1(sK2,sK1,X0_45,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_45,sK2,sK1) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_5302])).

cnf(c_5313,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5303])).

cnf(c_1099,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(sK4,X3_45,X2_45)
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(X4_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X4_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X3_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X1_45,X2_45,X0_45,k9_subset_1(X4_45,X3_45,X1_45)) != k2_partfun1(X3_45,X2_45,sK4,k9_subset_1(X4_45,X3_45,X1_45))
    | k2_partfun1(k4_subset_1(X4_45,X3_45,X1_45),X2_45,k1_tmap_1(X4_45,X2_45,X3_45,X1_45,sK4,X0_45),X1_45) = X0_45 ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_1336,plain,
    ( ~ v1_funct_2(sK5,X0_45,X1_45)
    | ~ v1_funct_2(sK4,X2_45,X1_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X3_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_45,X1_45,sK5,k9_subset_1(X3_45,X2_45,X0_45)) != k2_partfun1(X2_45,X1_45,sK4,k9_subset_1(X3_45,X2_45,X0_45))
    | k2_partfun1(k4_subset_1(X3_45,X2_45,X0_45),X1_45,k1_tmap_1(X3_45,X1_45,X2_45,X0_45,sK4,sK5),X0_45) = sK5 ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_1701,plain,
    ( ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_45))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_45,sK1,sK5,k9_subset_1(X1_45,sK2,X0_45)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1_45,sK2,X0_45))
    | k2_partfun1(k4_subset_1(X1_45,sK2,X0_45),sK1,k1_tmap_1(X1_45,sK1,sK2,X0_45,sK4,sK5),X0_45) = sK5 ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_2105,plain,
    ( ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_45,sK1,sK5,k9_subset_1(sK0,sK2,X0_45)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0_45))
    | k2_partfun1(k4_subset_1(sK0,sK2,X0_45),sK1,k1_tmap_1(sK0,sK1,sK2,X0_45,sK4,sK5),X0_45) = sK5 ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_3501,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_6280,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5313,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_13,c_12,c_1455,c_3501])).

cnf(c_212,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_646,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | k9_subset_1(X1_45,X0_45,X2_45) = k9_subset_1(X1_45,X2_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_630,plain,
    ( k9_subset_1(X0_45,X1_45,X2_45) = k9_subset_1(X0_45,X2_45,X1_45)
    | m1_subset_1(X1_45,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_1744,plain,
    ( k9_subset_1(sK0,X0_45,sK2) = k9_subset_1(sK0,sK2,X0_45) ),
    inference(superposition,[status(thm)],[c_646,c_630])).

cnf(c_214,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_644,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_1743,plain,
    ( k9_subset_1(sK0,X0_45,sK3) = k9_subset_1(sK0,sK3,X0_45) ),
    inference(superposition,[status(thm)],[c_644,c_630])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,k4_subset_1(X1,X2,X3),X4)
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X3),X3,X4)
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X2),X2,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X3))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X2))
    | k1_tmap_1(X1,X4,X2,X3,k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X2),k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X3)) = X0
    | k2_partfun1(X3,X4,k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X3),k9_subset_1(X1,X2,X3)) != k2_partfun1(X2,X4,k2_partfun1(k4_subset_1(X1,X2,X3),X4,X0,X2),k9_subset_1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_228,plain,
    ( ~ v1_funct_2(X0_45,k4_subset_1(X1_45,X2_45,X3_45),X4_45)
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X3_45),X3_45,X4_45)
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X2_45),X2_45,X4_45)
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X1_45))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(X1_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1_45,X2_45,X3_45),X4_45)))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X3_45),k1_zfmisc_1(k2_zfmisc_1(X3_45,X4_45)))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X2_45),k1_zfmisc_1(k2_zfmisc_1(X2_45,X4_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X3_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X3_45))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X2_45))
    | k1_tmap_1(X1_45,X4_45,X2_45,X3_45,k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X2_45),k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X3_45)) = X0_45
    | k2_partfun1(X3_45,X4_45,k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X3_45),k9_subset_1(X1_45,X2_45,X3_45)) != k2_partfun1(X2_45,X4_45,k2_partfun1(k4_subset_1(X1_45,X2_45,X3_45),X4_45,X0_45,X2_45),k9_subset_1(X1_45,X2_45,X3_45)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_631,plain,
    ( k1_tmap_1(X0_45,X1_45,X2_45,X3_45,k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X2_45),k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X3_45)) = X4_45
    | k2_partfun1(X3_45,X1_45,k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X3_45),k9_subset_1(X0_45,X2_45,X3_45)) != k2_partfun1(X2_45,X1_45,k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X2_45),k9_subset_1(X0_45,X2_45,X3_45))
    | v1_funct_2(X4_45,k4_subset_1(X0_45,X2_45,X3_45),X1_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X3_45),X3_45,X1_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X2_45),X2_45,X1_45) != iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X3_45,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X4_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0_45,X2_45,X3_45),X1_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X3_45),k1_zfmisc_1(k2_zfmisc_1(X3_45,X1_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X2_45),k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45))) != iProver_top
    | v1_xboole_0(X3_45) = iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_xboole_0(X2_45) = iProver_top
    | v1_xboole_0(X1_45) = iProver_top
    | v1_funct_1(X4_45) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X3_45)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(X0_45,X2_45,X3_45),X1_45,X4_45,X2_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_2437,plain,
    ( k1_tmap_1(sK0,X0_45,sK3,X1_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45)) = X2_45
    | k2_partfun1(X1_45,X0_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),k9_subset_1(sK0,X1_45,sK3)) != k2_partfun1(sK3,X0_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k9_subset_1(sK0,sK3,X1_45))
    | v1_funct_2(X2_45,k4_subset_1(sK0,sK3,X1_45),X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),X1_45,X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),sK3,X0_45) != iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X1_45),X0_45))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),k1_zfmisc_1(k2_zfmisc_1(X1_45,X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0_45))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_xboole_0(X1_45) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X2_45) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1743,c_631])).

cnf(c_3671,plain,
    ( m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),k1_zfmisc_1(k2_zfmisc_1(X1_45,X0_45))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X1_45),X0_45))) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),sK3,X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),X1_45,X0_45) != iProver_top
    | v1_funct_2(X2_45,k4_subset_1(sK0,sK3,X1_45),X0_45) != iProver_top
    | k2_partfun1(X1_45,X0_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),k9_subset_1(sK0,X1_45,sK3)) != k2_partfun1(sK3,X0_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k9_subset_1(sK0,sK3,X1_45))
    | k1_tmap_1(sK0,X0_45,sK3,X1_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45)) = X2_45
    | v1_xboole_0(X0_45) = iProver_top
    | v1_xboole_0(X1_45) = iProver_top
    | v1_funct_1(X2_45) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2437,c_24,c_28,c_29])).

cnf(c_3672,plain,
    ( k1_tmap_1(sK0,X0_45,sK3,X1_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45)) = X2_45
    | k2_partfun1(X1_45,X0_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),k9_subset_1(sK0,X1_45,sK3)) != k2_partfun1(sK3,X0_45,k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k9_subset_1(sK0,sK3,X1_45))
    | v1_funct_2(X2_45,k4_subset_1(sK0,sK3,X1_45),X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),X1_45,X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),sK3,X0_45) != iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X1_45),X0_45))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45),k1_zfmisc_1(k2_zfmisc_1(X1_45,X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0_45))) != iProver_top
    | v1_xboole_0(X1_45) = iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_funct_1(X2_45) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,X1_45)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK3,X1_45),X0_45,X2_45,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3671])).

cnf(c_3694,plain,
    ( k1_tmap_1(sK0,X0_45,sK3,sK2,k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK3),k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK2)) = X1_45
    | k2_partfun1(sK3,X0_45,k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK3),k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,X0_45,k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK2),k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X1_45,k4_subset_1(sK0,sK3,sK2),X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK3),sK3,X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK2),sK2,X0_45) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_45))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_funct_1(X1_45) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK3)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK3,sK2),X0_45,X1_45,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_3672])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X1_45))
    | k4_subset_1(X1_45,X0_45,X2_45) = k4_subset_1(X1_45,X2_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_629,plain,
    ( k4_subset_1(X0_45,X1_45,X2_45) = k4_subset_1(X0_45,X2_45,X1_45)
    | m1_subset_1(X1_45,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_1347,plain,
    ( k4_subset_1(sK0,sK3,X0_45) = k4_subset_1(sK0,X0_45,sK3)
    | m1_subset_1(X0_45,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_629])).

cnf(c_1493,plain,
    ( k4_subset_1(sK0,sK3,sK2) = k4_subset_1(sK0,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_646,c_1347])).

cnf(c_3730,plain,
    ( k1_tmap_1(sK0,X0_45,sK3,sK2,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2)) = X1_45
    | k2_partfun1(sK2,X0_45,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,X0_45,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X1_45,k4_subset_1(sK0,sK2,sK3),X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),sK3,X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),sK2,X0_45) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_45))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_funct_1(X1_45) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3694,c_1493])).

cnf(c_4217,plain,
    ( v1_xboole_0(X0_45) = iProver_top
    | k1_tmap_1(sK0,X0_45,sK3,sK2,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2)) = X1_45
    | k2_partfun1(sK2,X0_45,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,X0_45,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X1_45,k4_subset_1(sK0,sK2,sK3),X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),sK3,X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),sK2,X0_45) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_45))) != iProver_top
    | v1_funct_1(X1_45) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3730,c_26,c_27])).

cnf(c_4218,plain,
    ( k1_tmap_1(sK0,X0_45,sK3,sK2,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2)) = X1_45
    | k2_partfun1(sK2,X0_45,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,X0_45,k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X1_45,k4_subset_1(sK0,sK2,sK3),X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),sK3,X0_45) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),sK2,X0_45) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0_45))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_45))) != iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_funct_1(X1_45) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK3)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0_45,X1_45,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4217])).

cnf(c_6286,plain,
    ( k1_tmap_1(sK0,sK1,sK3,sK2,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)
    | k2_partfun1(sK2,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6280,c_4218])).

cnf(c_6299,plain,
    ( k1_tmap_1(sK0,sK1,sK3,sK2,sK5,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)
    | k2_partfun1(sK2,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) != iProver_top
    | v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6286,c_221,c_6280])).

cnf(c_258,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_233,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1146,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_1204,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_225,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(X3_45,X4_45,X2_45)
    | ~ m1_subset_1(X4_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(X4_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X5_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X3_45)
    | v1_funct_1(k1_tmap_1(X5_45,X2_45,X4_45,X1_45,X3_45,X0_45)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1059,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(sK4,X3_45,X2_45)
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(X4_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X4_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X3_45)
    | ~ v1_funct_1(X0_45)
    | v1_funct_1(k1_tmap_1(X4_45,X2_45,X3_45,X1_45,sK4,X0_45))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_1258,plain,
    ( ~ v1_funct_2(sK5,X0_45,X1_45)
    | ~ v1_funct_2(sK4,X2_45,X1_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X3_45)
    | v1_xboole_0(X0_45)
    | v1_funct_1(k1_tmap_1(X3_45,X1_45,X2_45,X0_45,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_1540,plain,
    ( ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_45))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | v1_funct_1(k1_tmap_1(X1_45,sK1,sK2,X0_45,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_1874,plain,
    ( ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0_45,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1540])).

cnf(c_3167,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_226,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(X3_45,X4_45,X2_45)
    | v1_funct_2(k1_tmap_1(X5_45,X2_45,X4_45,X1_45,X3_45,X0_45),k4_subset_1(X5_45,X4_45,X1_45),X2_45)
    | ~ m1_subset_1(X4_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(X4_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X5_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X3_45) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1069,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | v1_funct_2(k1_tmap_1(X3_45,X2_45,X4_45,X1_45,sK4,X0_45),k4_subset_1(X3_45,X4_45,X1_45),X2_45)
    | ~ v1_funct_2(sK4,X4_45,X2_45)
    | ~ m1_subset_1(X4_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X4_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X3_45)
    | v1_xboole_0(X4_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_1278,plain,
    ( v1_funct_2(k1_tmap_1(X0_45,X1_45,X2_45,X3_45,sK4,sK5),k4_subset_1(X0_45,X2_45,X3_45),X1_45)
    | ~ v1_funct_2(sK5,X3_45,X1_45)
    | ~ v1_funct_2(sK4,X2_45,X1_45)
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3_45,X1_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X3_45)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1593,plain,
    ( v1_funct_2(k1_tmap_1(X0_45,sK1,sK2,X1_45,sK4,sK5),k4_subset_1(X0_45,sK2,X1_45),sK1)
    | ~ v1_funct_2(sK5,X1_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_45))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_1894,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0_45,sK4,sK5),k4_subset_1(sK0,sK2,X0_45),sK1)
    | ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_3384,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_227,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(X3_45,X4_45,X2_45)
    | ~ m1_subset_1(X4_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X5_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(X4_45,X2_45)))
    | m1_subset_1(k1_tmap_1(X5_45,X2_45,X4_45,X1_45,X3_45,X0_45),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_45,X4_45,X1_45),X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X5_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X3_45) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1079,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(sK4,X3_45,X2_45)
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(X4_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X4_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | m1_subset_1(k1_tmap_1(X4_45,X2_45,X3_45,X1_45,sK4,X0_45),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4_45,X3_45,X1_45),X2_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_45,X2_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X4_45)
    | v1_xboole_0(X3_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_1298,plain,
    ( ~ v1_funct_2(sK5,X0_45,X1_45)
    | ~ v1_funct_2(sK4,X2_45,X1_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X3_45))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X3_45))
    | m1_subset_1(k1_tmap_1(X3_45,X1_45,X2_45,X0_45,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3_45,X2_45,X0_45),X1_45)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X2_45)
    | v1_xboole_0(X3_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_1613,plain,
    ( ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | m1_subset_1(k1_tmap_1(X1_45,sK1,sK2,X0_45,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1_45,sK2,X0_45),sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_45))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_2003,plain,
    ( ~ v1_funct_2(sK5,X0_45,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(sK0))
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0_45,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0_45),sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_45,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_3396,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2003])).

cnf(c_243,plain,
    ( ~ v1_funct_1(X0_45)
    | v1_funct_1(X1_45)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_977,plain,
    ( v1_funct_1(X0_45)
    | ~ v1_funct_1(sK4)
    | X0_45 != sK4 ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_6097,plain,
    ( v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0_45,X0_46)
    | m1_subset_1(X1_45,X1_46)
    | X1_46 != X0_46
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_1003,plain,
    ( m1_subset_1(X0_45,X0_46)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | X0_46 != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))
    | X0_45 != sK4 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_1145,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))
    | X0_45 != sK4 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_6096,plain,
    ( m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_242,plain,
    ( ~ v1_funct_2(X0_45,X1_45,X2_45)
    | v1_funct_2(X3_45,X4_45,X5_45)
    | X3_45 != X0_45
    | X4_45 != X1_45
    | X5_45 != X2_45 ),
    theory(equality)).

cnf(c_1023,plain,
    ( v1_funct_2(X0_45,X1_45,X2_45)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | X0_45 != sK4
    | X2_45 != sK1
    | X1_45 != sK2 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_1203,plain,
    ( v1_funct_2(X0_45,sK2,X1_45)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | X0_45 != sK4
    | X1_45 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_6095,plain,
    ( v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,X0_45)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | X0_45 != sK1
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_6103,plain,
    ( v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | sK1 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6095])).

cnf(c_6397,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ v1_funct_1(sK5)
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)
    | k2_partfun1(sK2,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6299])).

cnf(c_6453,plain,
    ( k1_tmap_1(sK0,sK1,sK3,sK2,sK5,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)
    | k2_partfun1(sK2,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6299,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_13,c_12,c_258,c_1146,c_1204,c_1455,c_3167,c_3384,c_3396,c_3405,c_6097,c_6096,c_6103,c_6397])).

cnf(c_9133,plain,
    ( k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_9128,c_6453])).

cnf(c_9134,plain,
    ( k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(equality_resolution_simp,[status(thm)],[c_9133])).

cnf(c_10,negated_conjecture,
    ( ~ r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK3,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_222,negated_conjecture,
    ( ~ r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK3,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_637,plain,
    ( r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK3,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_1561,plain,
    ( r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1493,c_637])).

cnf(c_9242,plain,
    ( r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9134,c_1561])).

cnf(c_9328,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) != iProver_top
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_9242])).

cnf(c_3397,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3396])).

cnf(c_3385,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) = iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3384])).

cnf(c_3168,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3167])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_31,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9328,c_3397,c_3385,c_3168,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_24])).


%------------------------------------------------------------------------------
