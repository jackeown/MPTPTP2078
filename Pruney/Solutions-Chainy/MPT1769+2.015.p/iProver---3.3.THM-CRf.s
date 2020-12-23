%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:04 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  165 (3221 expanded)
%              Number of clauses        :   90 ( 511 expanded)
%              Number of leaves         :   20 (1362 expanded)
%              Depth                    :   20
%              Number of atoms          :  998 (67395 expanded)
%              Number of equality atoms :  228 (4176 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
            | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
          & X0 = X3
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X6) )
     => ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK9),X5) )
        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK9),X5) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK9)
        & X0 = X3
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK9,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
              & X0 = X3
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ? [X6] :
            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK8)
              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK8) )
            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK8)
              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK8) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            & X0 = X3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X6) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                    | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                  & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                  & X0 = X3
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK7,X2),X5)
                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK7,X2),X5)
                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK7,X6)
                & X0 = X3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                      & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                        | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                      & X0 = X3
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X6) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK6,X2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK6,X2,X6),X5) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK6),u1_struct_0(X1),X4,X6)
                    & sK6 = X0
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
                    & v1_funct_2(X6,u1_struct_0(sK6),u1_struct_0(X1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                            | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                          & X0 = X3
                          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X6) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK5),X5)
                          | ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK5,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK5),X5)
                          | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK5,X6),X5) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                        & X0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK4),k2_tmap_1(X0,sK4,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK4),k3_tmap_1(X0,sK4,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK4),k2_tmap_1(X0,sK4,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK4),k3_tmap_1(X0,sK4,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(X3),u1_struct_0(sK4),X4,X6)
                            & X0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK4))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK4))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK4))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK4))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                & X0 = X3
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK3,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK3,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK3,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK3,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK3),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK3 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK3)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8)
      | ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8) )
    & ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8)
      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8) )
    & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK6),u1_struct_0(sK4),sK7,sK9)
    & sK3 = sK6
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    & v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK4))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK7)
    & m1_pre_topc(sK6,sK3)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f42,f49,f48,f47,f46,f45,f44,f43])).

fof(f91,plain,(
    r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK6),u1_struct_0(sK4),sK7,sK9) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    sK3 = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f92,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8)
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,
    ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8)
    | ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4051,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X5 = X4 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK6),u1_struct_0(sK4),sK7,sK9) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_653,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | u1_struct_0(sK6) != X4
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK4) != X5
    | u1_struct_0(sK4) != X2
    | sK9 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_654,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK9)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(u1_struct_0(sK4))
    | sK9 = sK7 ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_656,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | sK9 = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_32,c_31,c_30,c_26,c_25,c_24])).

cnf(c_4019,plain,
    ( sK9 = sK7
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4046,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4032,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4044,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5452,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4032,c_4044])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4054,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6667,plain,
    ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5452,c_4054])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4057,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7588,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6667,c_4057])).

cnf(c_9517,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4046,c_7588])).

cnf(c_9859,plain,
    ( sK9 = sK7
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4019,c_9517])).

cnf(c_10178,plain,
    ( k2_xboole_0(X0,sK7) = X1
    | sK9 = sK7
    | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
    | r2_hidden(sK2(X0,sK7,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_9859])).

cnf(c_4038,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( sK3 = sK6 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4102,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4038,c_23])).

cnf(c_5453,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4102,c_4044])).

cnf(c_6668,plain,
    ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5453,c_4054])).

cnf(c_7617,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6668,c_4057])).

cnf(c_9597,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4046,c_7617])).

cnf(c_9866,plain,
    ( sK9 = sK7
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4019,c_9597])).

cnf(c_11563,plain,
    ( k2_xboole_0(sK9,sK7) = X0
    | sK9 = sK7
    | r2_hidden(sK2(sK9,sK7,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10178,c_9866])).

cnf(c_11775,plain,
    ( k2_xboole_0(sK9,sK7) = sK9
    | sK9 = sK7 ),
    inference(superposition,[status(thm)],[c_11563,c_9866])).

cnf(c_11774,plain,
    ( k2_xboole_0(sK9,sK7) = sK7
    | sK9 = sK7 ),
    inference(superposition,[status(thm)],[c_11563,c_9859])).

cnf(c_11941,plain,
    ( sK9 = sK7 ),
    inference(superposition,[status(thm)],[c_11775,c_11774])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4029,plain,
    ( m1_pre_topc(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4084,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4029,c_23])).

cnf(c_35,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4027,plain,
    ( m1_pre_topc(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4042,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4041,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4232,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4042,c_4041])).

cnf(c_6404,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k3_tmap_1(X1,sK4,sK3,X0,sK9)
    | v1_funct_2(sK9,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4102,c_4232])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_46,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_47,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_48,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_59,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4037,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4091,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4037,c_23])).

cnf(c_7245,plain,
    ( v2_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k3_tmap_1(X1,sK4,sK3,X0,sK9)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6404,c_46,c_47,c_48,c_59,c_4091])).

cnf(c_7246,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k3_tmap_1(X1,sK4,sK3,X0,sK9)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7245])).

cnf(c_7257,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(sK5)) = k3_tmap_1(X0,sK4,sK3,sK5,sK9)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4027,c_7246])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4043,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5666,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k2_tmap_1(sK3,sK4,sK9,X0)
    | v1_funct_2(sK9,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4102,c_4043])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_43,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_44,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_45,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6155,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k2_tmap_1(sK3,sK4,sK9,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5666,c_43,c_44,c_45,c_46,c_47,c_48,c_59,c_4091])).

cnf(c_6156,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k2_tmap_1(sK3,sK4,sK9,X0)
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6155])).

cnf(c_6163,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(sK5)) = k2_tmap_1(sK3,sK4,sK9,sK5) ),
    inference(superposition,[status(thm)],[c_4027,c_6156])).

cnf(c_7275,plain,
    ( k3_tmap_1(X0,sK4,sK3,sK5,sK9) = k2_tmap_1(sK3,sK4,sK9,sK5)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7257,c_6163])).

cnf(c_8462,plain,
    ( k3_tmap_1(sK3,sK4,sK3,sK5,sK9) = k2_tmap_1(sK3,sK4,sK9,sK5)
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4084,c_7275])).

cnf(c_8636,plain,
    ( k3_tmap_1(sK3,sK4,sK3,sK5,sK9) = k2_tmap_1(sK3,sK4,sK9,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8462,c_43,c_44,c_45])).

cnf(c_21,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8)
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4039,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8) = iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4169,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK3,sK5,sK9),sK8) = iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4039,c_23])).

cnf(c_8639,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK9,sK5),sK8) = iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8636,c_4169])).

cnf(c_12933,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11941,c_8639])).

cnf(c_20,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8)
    | ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4040,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4174,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK3,sK5,sK9),sK8) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4040,c_23])).

cnf(c_8640,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK9,sK5),sK8) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8636,c_4174])).

cnf(c_12934,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11941,c_8640])).

cnf(c_12952,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12933,c_12934])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:33:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.78/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.98  
% 3.78/0.98  ------  iProver source info
% 3.78/0.98  
% 3.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.98  git: non_committed_changes: false
% 3.78/0.98  git: last_make_outside_of_git: false
% 3.78/0.98  
% 3.78/0.98  ------ 
% 3.78/0.98  
% 3.78/0.98  ------ Input Options
% 3.78/0.98  
% 3.78/0.98  --out_options                           all
% 3.78/0.98  --tptp_safe_out                         true
% 3.78/0.98  --problem_path                          ""
% 3.78/0.98  --include_path                          ""
% 3.78/0.98  --clausifier                            res/vclausify_rel
% 3.78/0.98  --clausifier_options                    --mode clausify
% 3.78/0.98  --stdin                                 false
% 3.78/0.98  --stats_out                             all
% 3.78/0.98  
% 3.78/0.98  ------ General Options
% 3.78/0.98  
% 3.78/0.98  --fof                                   false
% 3.78/0.98  --time_out_real                         305.
% 3.78/0.98  --time_out_virtual                      -1.
% 3.78/0.98  --symbol_type_check                     false
% 3.78/0.98  --clausify_out                          false
% 3.78/0.98  --sig_cnt_out                           false
% 3.78/0.98  --trig_cnt_out                          false
% 3.78/0.98  --trig_cnt_out_tolerance                1.
% 3.78/0.98  --trig_cnt_out_sk_spl                   false
% 3.78/0.98  --abstr_cl_out                          false
% 3.78/0.98  
% 3.78/0.98  ------ Global Options
% 3.78/0.98  
% 3.78/0.98  --schedule                              default
% 3.78/0.98  --add_important_lit                     false
% 3.78/0.98  --prop_solver_per_cl                    1000
% 3.78/0.98  --min_unsat_core                        false
% 3.78/0.98  --soft_assumptions                      false
% 3.78/0.98  --soft_lemma_size                       3
% 3.78/0.98  --prop_impl_unit_size                   0
% 3.78/0.98  --prop_impl_unit                        []
% 3.78/0.98  --share_sel_clauses                     true
% 3.78/0.98  --reset_solvers                         false
% 3.78/0.98  --bc_imp_inh                            [conj_cone]
% 3.78/0.98  --conj_cone_tolerance                   3.
% 3.78/0.98  --extra_neg_conj                        none
% 3.78/0.98  --large_theory_mode                     true
% 3.78/0.98  --prolific_symb_bound                   200
% 3.78/0.98  --lt_threshold                          2000
% 3.78/0.98  --clause_weak_htbl                      true
% 3.78/0.98  --gc_record_bc_elim                     false
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing Options
% 3.78/0.98  
% 3.78/0.98  --preprocessing_flag                    true
% 3.78/0.98  --time_out_prep_mult                    0.1
% 3.78/0.98  --splitting_mode                        input
% 3.78/0.98  --splitting_grd                         true
% 3.78/0.98  --splitting_cvd                         false
% 3.78/0.98  --splitting_cvd_svl                     false
% 3.78/0.98  --splitting_nvd                         32
% 3.78/0.98  --sub_typing                            true
% 3.78/0.98  --prep_gs_sim                           true
% 3.78/0.98  --prep_unflatten                        true
% 3.78/0.98  --prep_res_sim                          true
% 3.78/0.98  --prep_upred                            true
% 3.78/0.98  --prep_sem_filter                       exhaustive
% 3.78/0.98  --prep_sem_filter_out                   false
% 3.78/0.98  --pred_elim                             true
% 3.78/0.98  --res_sim_input                         true
% 3.78/0.98  --eq_ax_congr_red                       true
% 3.78/0.98  --pure_diseq_elim                       true
% 3.78/0.98  --brand_transform                       false
% 3.78/0.98  --non_eq_to_eq                          false
% 3.78/0.98  --prep_def_merge                        true
% 3.78/0.98  --prep_def_merge_prop_impl              false
% 3.78/0.98  --prep_def_merge_mbd                    true
% 3.78/0.98  --prep_def_merge_tr_red                 false
% 3.78/0.98  --prep_def_merge_tr_cl                  false
% 3.78/0.98  --smt_preprocessing                     true
% 3.78/0.98  --smt_ac_axioms                         fast
% 3.78/0.98  --preprocessed_out                      false
% 3.78/0.98  --preprocessed_stats                    false
% 3.78/0.98  
% 3.78/0.98  ------ Abstraction refinement Options
% 3.78/0.98  
% 3.78/0.98  --abstr_ref                             []
% 3.78/0.98  --abstr_ref_prep                        false
% 3.78/0.98  --abstr_ref_until_sat                   false
% 3.78/0.98  --abstr_ref_sig_restrict                funpre
% 3.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.98  --abstr_ref_under                       []
% 3.78/0.98  
% 3.78/0.98  ------ SAT Options
% 3.78/0.98  
% 3.78/0.98  --sat_mode                              false
% 3.78/0.98  --sat_fm_restart_options                ""
% 3.78/0.98  --sat_gr_def                            false
% 3.78/0.98  --sat_epr_types                         true
% 3.78/0.98  --sat_non_cyclic_types                  false
% 3.78/0.98  --sat_finite_models                     false
% 3.78/0.98  --sat_fm_lemmas                         false
% 3.78/0.98  --sat_fm_prep                           false
% 3.78/0.99  --sat_fm_uc_incr                        true
% 3.78/0.99  --sat_out_model                         small
% 3.78/0.99  --sat_out_clauses                       false
% 3.78/0.99  
% 3.78/0.99  ------ QBF Options
% 3.78/0.99  
% 3.78/0.99  --qbf_mode                              false
% 3.78/0.99  --qbf_elim_univ                         false
% 3.78/0.99  --qbf_dom_inst                          none
% 3.78/0.99  --qbf_dom_pre_inst                      false
% 3.78/0.99  --qbf_sk_in                             false
% 3.78/0.99  --qbf_pred_elim                         true
% 3.78/0.99  --qbf_split                             512
% 3.78/0.99  
% 3.78/0.99  ------ BMC1 Options
% 3.78/0.99  
% 3.78/0.99  --bmc1_incremental                      false
% 3.78/0.99  --bmc1_axioms                           reachable_all
% 3.78/0.99  --bmc1_min_bound                        0
% 3.78/0.99  --bmc1_max_bound                        -1
% 3.78/0.99  --bmc1_max_bound_default                -1
% 3.78/0.99  --bmc1_symbol_reachability              true
% 3.78/0.99  --bmc1_property_lemmas                  false
% 3.78/0.99  --bmc1_k_induction                      false
% 3.78/0.99  --bmc1_non_equiv_states                 false
% 3.78/0.99  --bmc1_deadlock                         false
% 3.78/0.99  --bmc1_ucm                              false
% 3.78/0.99  --bmc1_add_unsat_core                   none
% 3.78/0.99  --bmc1_unsat_core_children              false
% 3.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.99  --bmc1_out_stat                         full
% 3.78/0.99  --bmc1_ground_init                      false
% 3.78/0.99  --bmc1_pre_inst_next_state              false
% 3.78/0.99  --bmc1_pre_inst_state                   false
% 3.78/0.99  --bmc1_pre_inst_reach_state             false
% 3.78/0.99  --bmc1_out_unsat_core                   false
% 3.78/0.99  --bmc1_aig_witness_out                  false
% 3.78/0.99  --bmc1_verbose                          false
% 3.78/0.99  --bmc1_dump_clauses_tptp                false
% 3.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.99  --bmc1_dump_file                        -
% 3.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.99  --bmc1_ucm_extend_mode                  1
% 3.78/0.99  --bmc1_ucm_init_mode                    2
% 3.78/0.99  --bmc1_ucm_cone_mode                    none
% 3.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.99  --bmc1_ucm_relax_model                  4
% 3.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.99  --bmc1_ucm_layered_model                none
% 3.78/0.99  --bmc1_ucm_max_lemma_size               10
% 3.78/0.99  
% 3.78/0.99  ------ AIG Options
% 3.78/0.99  
% 3.78/0.99  --aig_mode                              false
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation Options
% 3.78/0.99  
% 3.78/0.99  --instantiation_flag                    true
% 3.78/0.99  --inst_sos_flag                         false
% 3.78/0.99  --inst_sos_phase                        true
% 3.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel_side                     num_symb
% 3.78/0.99  --inst_solver_per_active                1400
% 3.78/0.99  --inst_solver_calls_frac                1.
% 3.78/0.99  --inst_passive_queue_type               priority_queues
% 3.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.99  --inst_passive_queues_freq              [25;2]
% 3.78/0.99  --inst_dismatching                      true
% 3.78/0.99  --inst_eager_unprocessed_to_passive     true
% 3.78/0.99  --inst_prop_sim_given                   true
% 3.78/0.99  --inst_prop_sim_new                     false
% 3.78/0.99  --inst_subs_new                         false
% 3.78/0.99  --inst_eq_res_simp                      false
% 3.78/0.99  --inst_subs_given                       false
% 3.78/0.99  --inst_orphan_elimination               true
% 3.78/0.99  --inst_learning_loop_flag               true
% 3.78/0.99  --inst_learning_start                   3000
% 3.78/0.99  --inst_learning_factor                  2
% 3.78/0.99  --inst_start_prop_sim_after_learn       3
% 3.78/0.99  --inst_sel_renew                        solver
% 3.78/0.99  --inst_lit_activity_flag                true
% 3.78/0.99  --inst_restr_to_given                   false
% 3.78/0.99  --inst_activity_threshold               500
% 3.78/0.99  --inst_out_proof                        true
% 3.78/0.99  
% 3.78/0.99  ------ Resolution Options
% 3.78/0.99  
% 3.78/0.99  --resolution_flag                       true
% 3.78/0.99  --res_lit_sel                           adaptive
% 3.78/0.99  --res_lit_sel_side                      none
% 3.78/0.99  --res_ordering                          kbo
% 3.78/0.99  --res_to_prop_solver                    active
% 3.78/0.99  --res_prop_simpl_new                    false
% 3.78/0.99  --res_prop_simpl_given                  true
% 3.78/0.99  --res_passive_queue_type                priority_queues
% 3.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.99  --res_passive_queues_freq               [15;5]
% 3.78/0.99  --res_forward_subs                      full
% 3.78/0.99  --res_backward_subs                     full
% 3.78/0.99  --res_forward_subs_resolution           true
% 3.78/0.99  --res_backward_subs_resolution          true
% 3.78/0.99  --res_orphan_elimination                true
% 3.78/0.99  --res_time_limit                        2.
% 3.78/0.99  --res_out_proof                         true
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Options
% 3.78/0.99  
% 3.78/0.99  --superposition_flag                    true
% 3.78/0.99  --sup_passive_queue_type                priority_queues
% 3.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.99  --demod_completeness_check              fast
% 3.78/0.99  --demod_use_ground                      true
% 3.78/0.99  --sup_to_prop_solver                    passive
% 3.78/0.99  --sup_prop_simpl_new                    true
% 3.78/0.99  --sup_prop_simpl_given                  true
% 3.78/0.99  --sup_fun_splitting                     false
% 3.78/0.99  --sup_smt_interval                      50000
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Simplification Setup
% 3.78/0.99  
% 3.78/0.99  --sup_indices_passive                   []
% 3.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_full_bw                           [BwDemod]
% 3.78/0.99  --sup_immed_triv                        [TrivRules]
% 3.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_immed_bw_main                     []
% 3.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.99  
% 3.78/0.99  ------ Combination Options
% 3.78/0.99  
% 3.78/0.99  --comb_res_mult                         3
% 3.78/0.99  --comb_sup_mult                         2
% 3.78/0.99  --comb_inst_mult                        10
% 3.78/0.99  
% 3.78/0.99  ------ Debug Options
% 3.78/0.99  
% 3.78/0.99  --dbg_backtrace                         false
% 3.78/0.99  --dbg_dump_prop_clauses                 false
% 3.78/0.99  --dbg_dump_prop_clauses_file            -
% 3.78/0.99  --dbg_out_stat                          false
% 3.78/0.99  ------ Parsing...
% 3.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.99  ------ Proving...
% 3.78/0.99  ------ Problem Properties 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  clauses                                 41
% 3.78/0.99  conjectures                             22
% 3.78/0.99  EPR                                     17
% 3.78/0.99  Horn                                    33
% 3.78/0.99  unary                                   20
% 3.78/0.99  binary                                  13
% 3.78/0.99  lits                                    91
% 3.78/0.99  lits eq                                 8
% 3.78/0.99  fd_pure                                 0
% 3.78/0.99  fd_pseudo                               0
% 3.78/0.99  fd_cond                                 0
% 3.78/0.99  fd_pseudo_cond                          3
% 3.78/0.99  AC symbols                              0
% 3.78/0.99  
% 3.78/0.99  ------ Schedule dynamic 5 is on 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  Current options:
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options
% 3.78/0.99  
% 3.78/0.99  --out_options                           all
% 3.78/0.99  --tptp_safe_out                         true
% 3.78/0.99  --problem_path                          ""
% 3.78/0.99  --include_path                          ""
% 3.78/0.99  --clausifier                            res/vclausify_rel
% 3.78/0.99  --clausifier_options                    --mode clausify
% 3.78/0.99  --stdin                                 false
% 3.78/0.99  --stats_out                             all
% 3.78/0.99  
% 3.78/0.99  ------ General Options
% 3.78/0.99  
% 3.78/0.99  --fof                                   false
% 3.78/0.99  --time_out_real                         305.
% 3.78/0.99  --time_out_virtual                      -1.
% 3.78/0.99  --symbol_type_check                     false
% 3.78/0.99  --clausify_out                          false
% 3.78/0.99  --sig_cnt_out                           false
% 3.78/0.99  --trig_cnt_out                          false
% 3.78/0.99  --trig_cnt_out_tolerance                1.
% 3.78/0.99  --trig_cnt_out_sk_spl                   false
% 3.78/0.99  --abstr_cl_out                          false
% 3.78/0.99  
% 3.78/0.99  ------ Global Options
% 3.78/0.99  
% 3.78/0.99  --schedule                              default
% 3.78/0.99  --add_important_lit                     false
% 3.78/0.99  --prop_solver_per_cl                    1000
% 3.78/0.99  --min_unsat_core                        false
% 3.78/0.99  --soft_assumptions                      false
% 3.78/0.99  --soft_lemma_size                       3
% 3.78/0.99  --prop_impl_unit_size                   0
% 3.78/0.99  --prop_impl_unit                        []
% 3.78/0.99  --share_sel_clauses                     true
% 3.78/0.99  --reset_solvers                         false
% 3.78/0.99  --bc_imp_inh                            [conj_cone]
% 3.78/0.99  --conj_cone_tolerance                   3.
% 3.78/0.99  --extra_neg_conj                        none
% 3.78/0.99  --large_theory_mode                     true
% 3.78/0.99  --prolific_symb_bound                   200
% 3.78/0.99  --lt_threshold                          2000
% 3.78/0.99  --clause_weak_htbl                      true
% 3.78/0.99  --gc_record_bc_elim                     false
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing Options
% 3.78/0.99  
% 3.78/0.99  --preprocessing_flag                    true
% 3.78/0.99  --time_out_prep_mult                    0.1
% 3.78/0.99  --splitting_mode                        input
% 3.78/0.99  --splitting_grd                         true
% 3.78/0.99  --splitting_cvd                         false
% 3.78/0.99  --splitting_cvd_svl                     false
% 3.78/0.99  --splitting_nvd                         32
% 3.78/0.99  --sub_typing                            true
% 3.78/0.99  --prep_gs_sim                           true
% 3.78/0.99  --prep_unflatten                        true
% 3.78/0.99  --prep_res_sim                          true
% 3.78/0.99  --prep_upred                            true
% 3.78/0.99  --prep_sem_filter                       exhaustive
% 3.78/0.99  --prep_sem_filter_out                   false
% 3.78/0.99  --pred_elim                             true
% 3.78/0.99  --res_sim_input                         true
% 3.78/0.99  --eq_ax_congr_red                       true
% 3.78/0.99  --pure_diseq_elim                       true
% 3.78/0.99  --brand_transform                       false
% 3.78/0.99  --non_eq_to_eq                          false
% 3.78/0.99  --prep_def_merge                        true
% 3.78/0.99  --prep_def_merge_prop_impl              false
% 3.78/0.99  --prep_def_merge_mbd                    true
% 3.78/0.99  --prep_def_merge_tr_red                 false
% 3.78/0.99  --prep_def_merge_tr_cl                  false
% 3.78/0.99  --smt_preprocessing                     true
% 3.78/0.99  --smt_ac_axioms                         fast
% 3.78/0.99  --preprocessed_out                      false
% 3.78/0.99  --preprocessed_stats                    false
% 3.78/0.99  
% 3.78/0.99  ------ Abstraction refinement Options
% 3.78/0.99  
% 3.78/0.99  --abstr_ref                             []
% 3.78/0.99  --abstr_ref_prep                        false
% 3.78/0.99  --abstr_ref_until_sat                   false
% 3.78/0.99  --abstr_ref_sig_restrict                funpre
% 3.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.99  --abstr_ref_under                       []
% 3.78/0.99  
% 3.78/0.99  ------ SAT Options
% 3.78/0.99  
% 3.78/0.99  --sat_mode                              false
% 3.78/0.99  --sat_fm_restart_options                ""
% 3.78/0.99  --sat_gr_def                            false
% 3.78/0.99  --sat_epr_types                         true
% 3.78/0.99  --sat_non_cyclic_types                  false
% 3.78/0.99  --sat_finite_models                     false
% 3.78/0.99  --sat_fm_lemmas                         false
% 3.78/0.99  --sat_fm_prep                           false
% 3.78/0.99  --sat_fm_uc_incr                        true
% 3.78/0.99  --sat_out_model                         small
% 3.78/0.99  --sat_out_clauses                       false
% 3.78/0.99  
% 3.78/0.99  ------ QBF Options
% 3.78/0.99  
% 3.78/0.99  --qbf_mode                              false
% 3.78/0.99  --qbf_elim_univ                         false
% 3.78/0.99  --qbf_dom_inst                          none
% 3.78/0.99  --qbf_dom_pre_inst                      false
% 3.78/0.99  --qbf_sk_in                             false
% 3.78/0.99  --qbf_pred_elim                         true
% 3.78/0.99  --qbf_split                             512
% 3.78/0.99  
% 3.78/0.99  ------ BMC1 Options
% 3.78/0.99  
% 3.78/0.99  --bmc1_incremental                      false
% 3.78/0.99  --bmc1_axioms                           reachable_all
% 3.78/0.99  --bmc1_min_bound                        0
% 3.78/0.99  --bmc1_max_bound                        -1
% 3.78/0.99  --bmc1_max_bound_default                -1
% 3.78/0.99  --bmc1_symbol_reachability              true
% 3.78/0.99  --bmc1_property_lemmas                  false
% 3.78/0.99  --bmc1_k_induction                      false
% 3.78/0.99  --bmc1_non_equiv_states                 false
% 3.78/0.99  --bmc1_deadlock                         false
% 3.78/0.99  --bmc1_ucm                              false
% 3.78/0.99  --bmc1_add_unsat_core                   none
% 3.78/0.99  --bmc1_unsat_core_children              false
% 3.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.99  --bmc1_out_stat                         full
% 3.78/0.99  --bmc1_ground_init                      false
% 3.78/0.99  --bmc1_pre_inst_next_state              false
% 3.78/0.99  --bmc1_pre_inst_state                   false
% 3.78/0.99  --bmc1_pre_inst_reach_state             false
% 3.78/0.99  --bmc1_out_unsat_core                   false
% 3.78/0.99  --bmc1_aig_witness_out                  false
% 3.78/0.99  --bmc1_verbose                          false
% 3.78/0.99  --bmc1_dump_clauses_tptp                false
% 3.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.99  --bmc1_dump_file                        -
% 3.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.99  --bmc1_ucm_extend_mode                  1
% 3.78/0.99  --bmc1_ucm_init_mode                    2
% 3.78/0.99  --bmc1_ucm_cone_mode                    none
% 3.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.99  --bmc1_ucm_relax_model                  4
% 3.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.99  --bmc1_ucm_layered_model                none
% 3.78/0.99  --bmc1_ucm_max_lemma_size               10
% 3.78/0.99  
% 3.78/0.99  ------ AIG Options
% 3.78/0.99  
% 3.78/0.99  --aig_mode                              false
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation Options
% 3.78/0.99  
% 3.78/0.99  --instantiation_flag                    true
% 3.78/0.99  --inst_sos_flag                         false
% 3.78/0.99  --inst_sos_phase                        true
% 3.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel_side                     none
% 3.78/0.99  --inst_solver_per_active                1400
% 3.78/0.99  --inst_solver_calls_frac                1.
% 3.78/0.99  --inst_passive_queue_type               priority_queues
% 3.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.99  --inst_passive_queues_freq              [25;2]
% 3.78/0.99  --inst_dismatching                      true
% 3.78/0.99  --inst_eager_unprocessed_to_passive     true
% 3.78/0.99  --inst_prop_sim_given                   true
% 3.78/0.99  --inst_prop_sim_new                     false
% 3.78/0.99  --inst_subs_new                         false
% 3.78/0.99  --inst_eq_res_simp                      false
% 3.78/0.99  --inst_subs_given                       false
% 3.78/0.99  --inst_orphan_elimination               true
% 3.78/0.99  --inst_learning_loop_flag               true
% 3.78/0.99  --inst_learning_start                   3000
% 3.78/0.99  --inst_learning_factor                  2
% 3.78/0.99  --inst_start_prop_sim_after_learn       3
% 3.78/0.99  --inst_sel_renew                        solver
% 3.78/0.99  --inst_lit_activity_flag                true
% 3.78/0.99  --inst_restr_to_given                   false
% 3.78/0.99  --inst_activity_threshold               500
% 3.78/0.99  --inst_out_proof                        true
% 3.78/0.99  
% 3.78/0.99  ------ Resolution Options
% 3.78/0.99  
% 3.78/0.99  --resolution_flag                       false
% 3.78/0.99  --res_lit_sel                           adaptive
% 3.78/0.99  --res_lit_sel_side                      none
% 3.78/0.99  --res_ordering                          kbo
% 3.78/0.99  --res_to_prop_solver                    active
% 3.78/0.99  --res_prop_simpl_new                    false
% 3.78/0.99  --res_prop_simpl_given                  true
% 3.78/0.99  --res_passive_queue_type                priority_queues
% 3.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.99  --res_passive_queues_freq               [15;5]
% 3.78/0.99  --res_forward_subs                      full
% 3.78/0.99  --res_backward_subs                     full
% 3.78/0.99  --res_forward_subs_resolution           true
% 3.78/0.99  --res_backward_subs_resolution          true
% 3.78/0.99  --res_orphan_elimination                true
% 3.78/0.99  --res_time_limit                        2.
% 3.78/0.99  --res_out_proof                         true
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Options
% 3.78/0.99  
% 3.78/0.99  --superposition_flag                    true
% 3.78/0.99  --sup_passive_queue_type                priority_queues
% 3.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.99  --demod_completeness_check              fast
% 3.78/0.99  --demod_use_ground                      true
% 3.78/0.99  --sup_to_prop_solver                    passive
% 3.78/0.99  --sup_prop_simpl_new                    true
% 3.78/0.99  --sup_prop_simpl_given                  true
% 3.78/0.99  --sup_fun_splitting                     false
% 3.78/0.99  --sup_smt_interval                      50000
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Simplification Setup
% 3.78/0.99  
% 3.78/0.99  --sup_indices_passive                   []
% 3.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_full_bw                           [BwDemod]
% 3.78/0.99  --sup_immed_triv                        [TrivRules]
% 3.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_immed_bw_main                     []
% 3.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.99  
% 3.78/0.99  ------ Combination Options
% 3.78/0.99  
% 3.78/0.99  --comb_res_mult                         3
% 3.78/0.99  --comb_sup_mult                         2
% 3.78/0.99  --comb_inst_mult                        10
% 3.78/0.99  
% 3.78/0.99  ------ Debug Options
% 3.78/0.99  
% 3.78/0.99  --dbg_backtrace                         false
% 3.78/0.99  --dbg_dump_prop_clauses                 false
% 3.78/0.99  --dbg_dump_prop_clauses_file            -
% 3.78/0.99  --dbg_out_stat                          false
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ Proving...
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS status Theorem for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99   Resolution empty clause
% 3.78/0.99  
% 3.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  fof(f3,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f34,plain,(
% 3.78/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.78/0.99    inference(nnf_transformation,[],[f3])).
% 3.78/0.99  
% 3.78/0.99  fof(f35,plain,(
% 3.78/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.78/0.99    inference(flattening,[],[f34])).
% 3.78/0.99  
% 3.78/0.99  fof(f36,plain,(
% 3.78/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.78/0.99    inference(rectify,[],[f35])).
% 3.78/0.99  
% 3.78/0.99  fof(f37,plain,(
% 3.78/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f38,plain,(
% 3.78/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f59,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f38])).
% 3.78/0.99  
% 3.78/0.99  fof(f7,axiom,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f16,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.78/0.99    inference(ennf_transformation,[],[f7])).
% 3.78/0.99  
% 3.78/0.99  fof(f17,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.78/0.99    inference(flattening,[],[f16])).
% 3.78/0.99  
% 3.78/0.99  fof(f40,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.78/0.99    inference(nnf_transformation,[],[f17])).
% 3.78/0.99  
% 3.78/0.99  fof(f66,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f40])).
% 3.78/0.99  
% 3.78/0.99  fof(f11,conjecture,(
% 3.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f12,negated_conjecture,(
% 3.78/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.78/0.99    inference(negated_conjecture,[],[f11])).
% 3.78/0.99  
% 3.78/0.99  fof(f24,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f12])).
% 3.78/0.99  
% 3.78/0.99  fof(f25,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.78/0.99    inference(flattening,[],[f24])).
% 3.78/0.99  
% 3.78/0.99  fof(f41,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.78/0.99    inference(nnf_transformation,[],[f25])).
% 3.78/0.99  
% 3.78/0.99  fof(f42,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.78/0.99    inference(flattening,[],[f41])).
% 3.78/0.99  
% 3.78/0.99  fof(f49,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK9),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK9),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK9) & X0 = X3 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK9,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK9))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f48,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK8) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK8)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK8) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK8)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f47,plain,(
% 3.78/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK7,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK7,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK7,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f46,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK6,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK6,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK6),u1_struct_0(X1),X4,X6) & sK6 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f45,plain,(
% 3.78/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK5),X5) | ~r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK5,X6),X5)) & (r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK5),X5) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK5,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f44,plain,(
% 3.78/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK4),k2_tmap_1(X0,sK4,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK4),k3_tmap_1(X0,sK4,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK4),k2_tmap_1(X0,sK4,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK4),k3_tmap_1(X0,sK4,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(X3),u1_struct_0(sK4),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK4)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK4)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f43,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK3,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK3,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK3,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK3,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK3),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK3 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f50,plain,(
% 3.78/0.99    (((((((~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) | ~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8)) & (r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8)) & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK6),u1_struct_0(sK4),sK7,sK9) & sK3 = sK6 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK4)) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK7)) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f42,f49,f48,f47,f46,f45,f44,f43])).
% 3.78/0.99  
% 3.78/0.99  fof(f91,plain,(
% 3.78/0.99    r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK6),u1_struct_0(sK4),sK7,sK9)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f81,plain,(
% 3.78/0.99    v1_funct_1(sK7)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f82,plain,(
% 3.78/0.99    v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f83,plain,(
% 3.78/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f87,plain,(
% 3.78/0.99    v1_funct_1(sK9)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f88,plain,(
% 3.78/0.99    v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4))),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f89,plain,(
% 3.78/0.99    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f5,axiom,(
% 3.78/0.99    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f15,plain,(
% 3.78/0.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.78/0.99    inference(ennf_transformation,[],[f5])).
% 3.78/0.99  
% 3.78/0.99  fof(f63,plain,(
% 3.78/0.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f15])).
% 3.78/0.99  
% 3.78/0.99  fof(f6,axiom,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f39,plain,(
% 3.78/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.78/0.99    inference(nnf_transformation,[],[f6])).
% 3.78/0.99  
% 3.78/0.99  fof(f64,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f2,axiom,(
% 3.78/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f13,plain,(
% 3.78/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f2])).
% 3.78/0.99  
% 3.78/0.99  fof(f30,plain,(
% 3.78/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/0.99    inference(nnf_transformation,[],[f13])).
% 3.78/0.99  
% 3.78/0.99  fof(f31,plain,(
% 3.78/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/0.99    inference(rectify,[],[f30])).
% 3.78/0.99  
% 3.78/0.99  fof(f32,plain,(
% 3.78/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f33,plain,(
% 3.78/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.78/0.99  
% 3.78/0.99  fof(f53,plain,(
% 3.78/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f33])).
% 3.78/0.99  
% 3.78/0.99  fof(f1,axiom,(
% 3.78/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f26,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(nnf_transformation,[],[f1])).
% 3.78/0.99  
% 3.78/0.99  fof(f27,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(rectify,[],[f26])).
% 3.78/0.99  
% 3.78/0.99  fof(f28,plain,(
% 3.78/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f29,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f51,plain,(
% 3.78/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f29])).
% 3.78/0.99  
% 3.78/0.99  fof(f90,plain,(
% 3.78/0.99    sK3 = sK6),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f80,plain,(
% 3.78/0.99    m1_pre_topc(sK6,sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f78,plain,(
% 3.78/0.99    m1_pre_topc(sK5,sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f9,axiom,(
% 3.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f20,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f9])).
% 3.78/0.99  
% 3.78/0.99  fof(f21,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/0.99    inference(flattening,[],[f20])).
% 3.78/0.99  
% 3.78/0.99  fof(f69,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f21])).
% 3.78/0.99  
% 3.78/0.99  fof(f10,axiom,(
% 3.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f22,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f10])).
% 3.78/0.99  
% 3.78/0.99  fof(f23,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.99    inference(flattening,[],[f22])).
% 3.78/0.99  
% 3.78/0.99  fof(f70,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f23])).
% 3.78/0.99  
% 3.78/0.99  fof(f74,plain,(
% 3.78/0.99    ~v2_struct_0(sK4)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f75,plain,(
% 3.78/0.99    v2_pre_topc(sK4)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f76,plain,(
% 3.78/0.99    l1_pre_topc(sK4)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f8,axiom,(
% 3.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f18,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f8])).
% 3.78/0.99  
% 3.78/0.99  fof(f19,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/0.99    inference(flattening,[],[f18])).
% 3.78/0.99  
% 3.78/0.99  fof(f68,plain,(
% 3.78/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f19])).
% 3.78/0.99  
% 3.78/0.99  fof(f71,plain,(
% 3.78/0.99    ~v2_struct_0(sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f72,plain,(
% 3.78/0.99    v2_pre_topc(sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f73,plain,(
% 3.78/0.99    l1_pre_topc(sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f92,plain,(
% 3.78/0.99    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f93,plain,(
% 3.78/0.99    ~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) | ~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8)),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7,plain,
% 3.78/0.99      ( r2_hidden(sK2(X0,X1,X2),X1)
% 3.78/0.99      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.78/0.99      | r2_hidden(sK2(X0,X1,X2),X0)
% 3.78/0.99      | k2_xboole_0(X0,X1) = X2 ),
% 3.78/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4051,plain,
% 3.78/0.99      ( k2_xboole_0(X0,X1) = X2
% 3.78/0.99      | r2_hidden(sK2(X0,X1,X2),X1) = iProver_top
% 3.78/0.99      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 3.78/0.99      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_16,plain,
% 3.78/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.78/0.99      | ~ v1_funct_2(X5,X2,X3)
% 3.78/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.78/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.78/0.99      | ~ v1_funct_1(X5)
% 3.78/0.99      | ~ v1_funct_1(X4)
% 3.78/0.99      | v1_xboole_0(X1)
% 3.78/0.99      | v1_xboole_0(X3)
% 3.78/0.99      | X5 = X4 ),
% 3.78/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_22,negated_conjecture,
% 3.78/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK6),u1_struct_0(sK4),sK7,sK9) ),
% 3.78/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_653,plain,
% 3.78/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.99      | ~ v1_funct_2(X3,X4,X5)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.78/0.99      | ~ v1_funct_1(X3)
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | v1_xboole_0(X2)
% 3.78/0.99      | v1_xboole_0(X5)
% 3.78/0.99      | X3 = X0
% 3.78/0.99      | u1_struct_0(sK6) != X4
% 3.78/0.99      | u1_struct_0(sK3) != X1
% 3.78/0.99      | u1_struct_0(sK4) != X5
% 3.78/0.99      | u1_struct_0(sK4) != X2
% 3.78/0.99      | sK9 != X3
% 3.78/0.99      | sK7 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_654,plain,
% 3.78/0.99      ( ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4))
% 3.78/0.99      | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
% 3.78/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
% 3.78/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 3.78/0.99      | ~ v1_funct_1(sK9)
% 3.78/0.99      | ~ v1_funct_1(sK7)
% 3.78/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 3.78/0.99      | sK9 = sK7 ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_653]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_32,negated_conjecture,
% 3.78/0.99      ( v1_funct_1(sK7) ),
% 3.78/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_31,negated_conjecture,
% 3.78/0.99      ( v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_30,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_26,negated_conjecture,
% 3.78/0.99      ( v1_funct_1(sK9) ),
% 3.78/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_25,negated_conjecture,
% 3.78/0.99      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_24,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_656,plain,
% 3.78/0.99      ( v1_xboole_0(u1_struct_0(sK4)) | sK9 = sK7 ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_654,c_32,c_31,c_30,c_26,c_25,c_24]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4019,plain,
% 3.78/0.99      ( sK9 = sK7 | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12,plain,
% 3.78/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4046,plain,
% 3.78/0.99      ( v1_xboole_0(X0) != iProver_top
% 3.78/0.99      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4032,plain,
% 3.78/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4044,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.78/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5452,plain,
% 3.78/0.99      ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4032,c_4044]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4054,plain,
% 3.78/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.78/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.78/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6667,plain,
% 3.78/0.99      ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top
% 3.78/0.99      | r2_hidden(X0,sK7) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5452,c_4054]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1,plain,
% 3.78/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4057,plain,
% 3.78/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7588,plain,
% 3.78/0.99      ( r2_hidden(X0,sK7) != iProver_top
% 3.78/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_6667,c_4057]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9517,plain,
% 3.78/0.99      ( r2_hidden(X0,sK7) != iProver_top
% 3.78/0.99      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4046,c_7588]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9859,plain,
% 3.78/0.99      ( sK9 = sK7 | r2_hidden(X0,sK7) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4019,c_9517]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_10178,plain,
% 3.78/0.99      ( k2_xboole_0(X0,sK7) = X1
% 3.78/0.99      | sK9 = sK7
% 3.78/0.99      | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
% 3.78/0.99      | r2_hidden(sK2(X0,sK7,X1),X0) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4051,c_9859]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4038,plain,
% 3.78/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_23,negated_conjecture,
% 3.78/0.99      ( sK3 = sK6 ),
% 3.78/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4102,plain,
% 3.78/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_4038,c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5453,plain,
% 3.78/0.99      ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4102,c_4044]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6668,plain,
% 3.78/0.99      ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top
% 3.78/0.99      | r2_hidden(X0,sK9) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5453,c_4054]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7617,plain,
% 3.78/0.99      ( r2_hidden(X0,sK9) != iProver_top
% 3.78/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_6668,c_4057]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9597,plain,
% 3.78/0.99      ( r2_hidden(X0,sK9) != iProver_top
% 3.78/0.99      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4046,c_7617]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9866,plain,
% 3.78/0.99      ( sK9 = sK7 | r2_hidden(X0,sK9) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4019,c_9597]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11563,plain,
% 3.78/0.99      ( k2_xboole_0(sK9,sK7) = X0
% 3.78/0.99      | sK9 = sK7
% 3.78/0.99      | r2_hidden(sK2(sK9,sK7,X0),X0) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_10178,c_9866]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11775,plain,
% 3.78/0.99      ( k2_xboole_0(sK9,sK7) = sK9 | sK9 = sK7 ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_11563,c_9866]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11774,plain,
% 3.78/0.99      ( k2_xboole_0(sK9,sK7) = sK7 | sK9 = sK7 ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_11563,c_9859]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11941,plain,
% 3.78/0.99      ( sK9 = sK7 ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_11775,c_11774]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_33,negated_conjecture,
% 3.78/0.99      ( m1_pre_topc(sK6,sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4029,plain,
% 3.78/0.99      ( m1_pre_topc(sK6,sK3) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4084,plain,
% 3.78/0.99      ( m1_pre_topc(sK3,sK3) = iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_4029,c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_35,negated_conjecture,
% 3.78/0.99      ( m1_pre_topc(sK5,sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4027,plain,
% 3.78/0.99      ( m1_pre_topc(sK5,sK3) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_18,plain,
% 3.78/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.78/0.99      | ~ m1_pre_topc(X3,X4)
% 3.78/0.99      | ~ m1_pre_topc(X3,X1)
% 3.78/0.99      | ~ m1_pre_topc(X1,X4)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.78/0.99      | v2_struct_0(X4)
% 3.78/0.99      | v2_struct_0(X2)
% 3.78/0.99      | ~ v2_pre_topc(X2)
% 3.78/0.99      | ~ v2_pre_topc(X4)
% 3.78/0.99      | ~ l1_pre_topc(X2)
% 3.78/0.99      | ~ l1_pre_topc(X4)
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4042,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.78/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.78/0.99      | m1_pre_topc(X3,X4) != iProver_top
% 3.78/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.78/0.99      | m1_pre_topc(X0,X4) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.78/0.99      | v2_struct_0(X4) = iProver_top
% 3.78/0.99      | v2_struct_0(X1) = iProver_top
% 3.78/0.99      | v2_pre_topc(X1) != iProver_top
% 3.78/0.99      | v2_pre_topc(X4) != iProver_top
% 3.78/0.99      | l1_pre_topc(X1) != iProver_top
% 3.78/0.99      | l1_pre_topc(X4) != iProver_top
% 3.78/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_19,plain,
% 3.78/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.78/0.99      | ~ m1_pre_topc(X1,X2)
% 3.78/0.99      | m1_pre_topc(X0,X2)
% 3.78/0.99      | ~ v2_pre_topc(X2)
% 3.78/0.99      | ~ l1_pre_topc(X2) ),
% 3.78/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4041,plain,
% 3.78/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.78/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 3.78/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 3.78/0.99      | v2_pre_topc(X2) != iProver_top
% 3.78/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4232,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.78/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.78/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.78/0.99      | m1_pre_topc(X0,X4) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.78/0.99      | v2_struct_0(X4) = iProver_top
% 3.78/0.99      | v2_struct_0(X1) = iProver_top
% 3.78/0.99      | v2_pre_topc(X4) != iProver_top
% 3.78/0.99      | v2_pre_topc(X1) != iProver_top
% 3.78/0.99      | l1_pre_topc(X4) != iProver_top
% 3.78/0.99      | l1_pre_topc(X1) != iProver_top
% 3.78/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.78/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4042,c_4041]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6404,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k3_tmap_1(X1,sK4,sK3,X0,sK9)
% 3.78/0.99      | v1_funct_2(sK9,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 3.78/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.78/0.99      | m1_pre_topc(sK3,X1) != iProver_top
% 3.78/0.99      | v2_struct_0(X1) = iProver_top
% 3.78/0.99      | v2_struct_0(sK4) = iProver_top
% 3.78/0.99      | v2_pre_topc(X1) != iProver_top
% 3.78/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.78/0.99      | l1_pre_topc(X1) != iProver_top
% 3.78/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.78/0.99      | v1_funct_1(sK9) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4102,c_4232]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_39,negated_conjecture,
% 3.78/0.99      ( ~ v2_struct_0(sK4) ),
% 3.78/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_46,plain,
% 3.78/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_38,negated_conjecture,
% 3.78/0.99      ( v2_pre_topc(sK4) ),
% 3.78/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_47,plain,
% 3.78/0.99      ( v2_pre_topc(sK4) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_37,negated_conjecture,
% 3.78/0.99      ( l1_pre_topc(sK4) ),
% 3.78/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_48,plain,
% 3.78/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_59,plain,
% 3.78/0.99      ( v1_funct_1(sK9) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4037,plain,
% 3.78/0.99      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK4)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4091,plain,
% 3.78/0.99      ( v1_funct_2(sK9,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_4037,c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7245,plain,
% 3.78/0.99      ( v2_pre_topc(X1) != iProver_top
% 3.78/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k3_tmap_1(X1,sK4,sK3,X0,sK9)
% 3.78/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.78/0.99      | m1_pre_topc(sK3,X1) != iProver_top
% 3.78/0.99      | v2_struct_0(X1) = iProver_top
% 3.78/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_6404,c_46,c_47,c_48,c_59,c_4091]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7246,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k3_tmap_1(X1,sK4,sK3,X0,sK9)
% 3.78/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.78/0.99      | m1_pre_topc(sK3,X1) != iProver_top
% 3.78/0.99      | v2_struct_0(X1) = iProver_top
% 3.78/0.99      | v2_pre_topc(X1) != iProver_top
% 3.78/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_7245]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7257,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(sK5)) = k3_tmap_1(X0,sK4,sK3,sK5,sK9)
% 3.78/0.99      | m1_pre_topc(sK3,X0) != iProver_top
% 3.78/0.99      | v2_struct_0(X0) = iProver_top
% 3.78/0.99      | v2_pre_topc(X0) != iProver_top
% 3.78/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4027,c_7246]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_17,plain,
% 3.78/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.78/0.99      | ~ m1_pre_topc(X3,X1)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.78/0.99      | v2_struct_0(X1)
% 3.78/0.99      | v2_struct_0(X2)
% 3.78/0.99      | ~ v2_pre_topc(X2)
% 3.78/0.99      | ~ v2_pre_topc(X1)
% 3.78/0.99      | ~ l1_pre_topc(X2)
% 3.78/0.99      | ~ l1_pre_topc(X1)
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4043,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 3.78/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.78/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.78/0.99      | v2_struct_0(X1) = iProver_top
% 3.78/0.99      | v2_struct_0(X0) = iProver_top
% 3.78/0.99      | v2_pre_topc(X1) != iProver_top
% 3.78/0.99      | v2_pre_topc(X0) != iProver_top
% 3.78/0.99      | l1_pre_topc(X1) != iProver_top
% 3.78/0.99      | l1_pre_topc(X0) != iProver_top
% 3.78/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5666,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k2_tmap_1(sK3,sK4,sK9,X0)
% 3.78/0.99      | v1_funct_2(sK9,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 3.78/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.78/0.99      | v2_struct_0(sK3) = iProver_top
% 3.78/0.99      | v2_struct_0(sK4) = iProver_top
% 3.78/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.78/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.78/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.78/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.78/0.99      | v1_funct_1(sK9) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4102,c_4043]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_42,negated_conjecture,
% 3.78/0.99      ( ~ v2_struct_0(sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_43,plain,
% 3.78/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_41,negated_conjecture,
% 3.78/0.99      ( v2_pre_topc(sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_44,plain,
% 3.78/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_40,negated_conjecture,
% 3.78/0.99      ( l1_pre_topc(sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_45,plain,
% 3.78/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6155,plain,
% 3.78/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.78/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k2_tmap_1(sK3,sK4,sK9,X0) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_5666,c_43,c_44,c_45,c_46,c_47,c_48,c_59,c_4091]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6156,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(X0)) = k2_tmap_1(sK3,sK4,sK9,X0)
% 3.78/0.99      | m1_pre_topc(X0,sK3) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_6155]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6163,plain,
% 3.78/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK4),sK9,u1_struct_0(sK5)) = k2_tmap_1(sK3,sK4,sK9,sK5) ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4027,c_6156]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7275,plain,
% 3.78/0.99      ( k3_tmap_1(X0,sK4,sK3,sK5,sK9) = k2_tmap_1(sK3,sK4,sK9,sK5)
% 3.78/0.99      | m1_pre_topc(sK3,X0) != iProver_top
% 3.78/0.99      | v2_struct_0(X0) = iProver_top
% 3.78/0.99      | v2_pre_topc(X0) != iProver_top
% 3.78/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_7257,c_6163]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8462,plain,
% 3.78/0.99      ( k3_tmap_1(sK3,sK4,sK3,sK5,sK9) = k2_tmap_1(sK3,sK4,sK9,sK5)
% 3.78/0.99      | v2_struct_0(sK3) = iProver_top
% 3.78/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.78/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4084,c_7275]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8636,plain,
% 3.78/0.99      ( k3_tmap_1(sK3,sK4,sK3,sK5,sK9) = k2_tmap_1(sK3,sK4,sK9,sK5) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_8462,c_43,c_44,c_45]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_21,negated_conjecture,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8)
% 3.78/0.99      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) ),
% 3.78/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4039,plain,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8) = iProver_top
% 3.78/0.99      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4169,plain,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK3,sK5,sK9),sK8) = iProver_top
% 3.78/0.99      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) = iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_4039,c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8639,plain,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK9,sK5),sK8) = iProver_top
% 3.78/0.99      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) = iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_8636,c_4169]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12933,plain,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) = iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_11941,c_8639]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_20,negated_conjecture,
% 3.78/0.99      ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8)
% 3.78/0.99      | ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) ),
% 3.78/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4040,plain,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK6,sK5,sK9),sK8) != iProver_top
% 3.78/0.99      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4174,plain,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k3_tmap_1(sK3,sK4,sK3,sK5,sK9),sK8) != iProver_top
% 3.78/0.99      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) != iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_4040,c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8640,plain,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK9,sK5),sK8) != iProver_top
% 3.78/0.99      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) != iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_8636,c_4174]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12934,plain,
% 3.78/0.99      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),k2_tmap_1(sK3,sK4,sK7,sK5),sK8) != iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_11941,c_8640]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12952,plain,
% 3.78/0.99      ( $false ),
% 3.78/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_12933,c_12934]) ).
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  ------                               Statistics
% 3.78/0.99  
% 3.78/0.99  ------ General
% 3.78/0.99  
% 3.78/0.99  abstr_ref_over_cycles:                  0
% 3.78/0.99  abstr_ref_under_cycles:                 0
% 3.78/0.99  gc_basic_clause_elim:                   0
% 3.78/0.99  forced_gc_time:                         0
% 3.78/0.99  parsing_time:                           0.011
% 3.78/0.99  unif_index_cands_time:                  0.
% 3.78/0.99  unif_index_add_time:                    0.
% 3.78/0.99  orderings_time:                         0.
% 3.78/0.99  out_proof_time:                         0.012
% 3.78/0.99  total_time:                             0.386
% 3.78/0.99  num_of_symbols:                         60
% 3.78/0.99  num_of_terms:                           10672
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing
% 3.78/0.99  
% 3.78/0.99  num_of_splits:                          0
% 3.78/0.99  num_of_split_atoms:                     0
% 3.78/0.99  num_of_reused_defs:                     0
% 3.78/0.99  num_eq_ax_congr_red:                    33
% 3.78/0.99  num_of_sem_filtered_clauses:            1
% 3.78/0.99  num_of_subtypes:                        0
% 3.78/0.99  monotx_restored_types:                  0
% 3.78/0.99  sat_num_of_epr_types:                   0
% 3.78/0.99  sat_num_of_non_cyclic_types:            0
% 3.78/0.99  sat_guarded_non_collapsed_types:        0
% 3.78/0.99  num_pure_diseq_elim:                    0
% 3.78/0.99  simp_replaced_by:                       0
% 3.78/0.99  res_preprocessed:                       203
% 3.78/0.99  prep_upred:                             0
% 3.78/0.99  prep_unflattend:                        58
% 3.78/0.99  smt_new_axioms:                         0
% 3.78/0.99  pred_elim_cands:                        11
% 3.78/0.99  pred_elim:                              1
% 3.78/0.99  pred_elim_cl:                           2
% 3.78/0.99  pred_elim_cycles:                       9
% 3.78/0.99  merged_defs:                            16
% 3.78/0.99  merged_defs_ncl:                        0
% 3.78/0.99  bin_hyper_res:                          16
% 3.78/0.99  prep_cycles:                            4
% 3.78/0.99  pred_elim_time:                         0.055
% 3.78/0.99  splitting_time:                         0.
% 3.78/0.99  sem_filter_time:                        0.
% 3.78/0.99  monotx_time:                            0.
% 3.78/0.99  subtype_inf_time:                       0.
% 3.78/0.99  
% 3.78/0.99  ------ Problem properties
% 3.78/0.99  
% 3.78/0.99  clauses:                                41
% 3.78/0.99  conjectures:                            22
% 3.78/0.99  epr:                                    17
% 3.78/0.99  horn:                                   33
% 3.78/0.99  ground:                                 23
% 3.78/0.99  unary:                                  20
% 3.78/0.99  binary:                                 13
% 3.78/0.99  lits:                                   91
% 3.78/0.99  lits_eq:                                8
% 3.78/0.99  fd_pure:                                0
% 3.78/0.99  fd_pseudo:                              0
% 3.78/0.99  fd_cond:                                0
% 3.78/0.99  fd_pseudo_cond:                         3
% 3.78/0.99  ac_symbols:                             0
% 3.78/0.99  
% 3.78/0.99  ------ Propositional Solver
% 3.78/0.99  
% 3.78/0.99  prop_solver_calls:                      29
% 3.78/0.99  prop_fast_solver_calls:                 2321
% 3.78/0.99  smt_solver_calls:                       0
% 3.78/0.99  smt_fast_solver_calls:                  0
% 3.78/0.99  prop_num_of_clauses:                    4118
% 3.78/0.99  prop_preprocess_simplified:             11452
% 3.78/0.99  prop_fo_subsumed:                       116
% 3.78/0.99  prop_solver_time:                       0.
% 3.78/0.99  smt_solver_time:                        0.
% 3.78/0.99  smt_fast_solver_time:                   0.
% 3.78/0.99  prop_fast_solver_time:                  0.
% 3.78/0.99  prop_unsat_core_time:                   0.
% 3.78/0.99  
% 3.78/0.99  ------ QBF
% 3.78/0.99  
% 3.78/0.99  qbf_q_res:                              0
% 3.78/0.99  qbf_num_tautologies:                    0
% 3.78/0.99  qbf_prep_cycles:                        0
% 3.78/0.99  
% 3.78/0.99  ------ BMC1
% 3.78/0.99  
% 3.78/0.99  bmc1_current_bound:                     -1
% 3.78/0.99  bmc1_last_solved_bound:                 -1
% 3.78/0.99  bmc1_unsat_core_size:                   -1
% 3.78/0.99  bmc1_unsat_core_parents_size:           -1
% 3.78/0.99  bmc1_merge_next_fun:                    0
% 3.78/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation
% 3.78/0.99  
% 3.78/0.99  inst_num_of_clauses:                    1015
% 3.78/0.99  inst_num_in_passive:                    487
% 3.78/0.99  inst_num_in_active:                     493
% 3.78/0.99  inst_num_in_unprocessed:                35
% 3.78/0.99  inst_num_of_loops:                      570
% 3.78/0.99  inst_num_of_learning_restarts:          0
% 3.78/0.99  inst_num_moves_active_passive:          74
% 3.78/0.99  inst_lit_activity:                      0
% 3.78/0.99  inst_lit_activity_moves:                0
% 3.78/0.99  inst_num_tautologies:                   0
% 3.78/0.99  inst_num_prop_implied:                  0
% 3.78/0.99  inst_num_existing_simplified:           0
% 3.78/0.99  inst_num_eq_res_simplified:             0
% 3.78/0.99  inst_num_child_elim:                    0
% 3.78/0.99  inst_num_of_dismatching_blockings:      249
% 3.78/0.99  inst_num_of_non_proper_insts:           892
% 3.78/0.99  inst_num_of_duplicates:                 0
% 3.78/0.99  inst_inst_num_from_inst_to_res:         0
% 3.78/0.99  inst_dismatching_checking_time:         0.
% 3.78/0.99  
% 3.78/0.99  ------ Resolution
% 3.78/0.99  
% 3.78/0.99  res_num_of_clauses:                     0
% 3.78/0.99  res_num_in_passive:                     0
% 3.78/0.99  res_num_in_active:                      0
% 3.78/0.99  res_num_of_loops:                       207
% 3.78/0.99  res_forward_subset_subsumed:            66
% 3.78/0.99  res_backward_subset_subsumed:           0
% 3.78/0.99  res_forward_subsumed:                   0
% 3.78/0.99  res_backward_subsumed:                  0
% 3.78/0.99  res_forward_subsumption_resolution:     7
% 3.78/0.99  res_backward_subsumption_resolution:    0
% 3.78/0.99  res_clause_to_clause_subsumption:       819
% 3.78/0.99  res_orphan_elimination:                 0
% 3.78/0.99  res_tautology_del:                      82
% 3.78/0.99  res_num_eq_res_simplified:              0
% 3.78/0.99  res_num_sel_changes:                    0
% 3.78/0.99  res_moves_from_active_to_pass:          0
% 3.78/0.99  
% 3.78/0.99  ------ Superposition
% 3.78/0.99  
% 3.78/0.99  sup_time_total:                         0.
% 3.78/0.99  sup_time_generating:                    0.
% 3.78/0.99  sup_time_sim_full:                      0.
% 3.78/0.99  sup_time_sim_immed:                     0.
% 3.78/0.99  
% 3.78/0.99  sup_num_of_clauses:                     147
% 3.78/0.99  sup_num_in_active:                      73
% 3.78/0.99  sup_num_in_passive:                     74
% 3.78/0.99  sup_num_of_loops:                       112
% 3.78/0.99  sup_fw_superposition:                   135
% 3.78/0.99  sup_bw_superposition:                   110
% 3.78/0.99  sup_immediate_simplified:               42
% 3.78/0.99  sup_given_eliminated:                   1
% 3.78/0.99  comparisons_done:                       0
% 3.78/0.99  comparisons_avoided:                    12
% 3.78/0.99  
% 3.78/0.99  ------ Simplifications
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  sim_fw_subset_subsumed:                 16
% 3.78/0.99  sim_bw_subset_subsumed:                 21
% 3.78/0.99  sim_fw_subsumed:                        19
% 3.78/0.99  sim_bw_subsumed:                        0
% 3.78/0.99  sim_fw_subsumption_res:                 5
% 3.78/0.99  sim_bw_subsumption_res:                 0
% 3.78/0.99  sim_tautology_del:                      32
% 3.78/0.99  sim_eq_tautology_del:                   1
% 3.78/0.99  sim_eq_res_simp:                        7
% 3.78/0.99  sim_fw_demodulated:                     3
% 3.78/0.99  sim_bw_demodulated:                     28
% 3.78/0.99  sim_light_normalised:                   10
% 3.78/0.99  sim_joinable_taut:                      0
% 3.78/0.99  sim_joinable_simp:                      0
% 3.78/0.99  sim_ac_normalised:                      0
% 3.78/0.99  sim_smt_subsumption:                    0
% 3.78/0.99  
%------------------------------------------------------------------------------
