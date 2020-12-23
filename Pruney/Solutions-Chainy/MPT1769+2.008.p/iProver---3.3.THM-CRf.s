%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:03 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  173 (1847 expanded)
%              Number of clauses        :   97 ( 309 expanded)
%              Number of leaves         :   19 ( 772 expanded)
%              Depth                    :   20
%              Number of atoms          :  961 (38269 expanded)
%              Number of equality atoms :  231 (2446 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f14])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f44,plain,(
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
          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5) )
        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK8)
        & X0 = X3
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7)
              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7) )
            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7)
              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            & X0 = X3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X6) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5)
                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5)
                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK6,X6)
                & X0 = X3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
                      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK5),u1_struct_0(X1),X4,X6)
                    & sK5 = X0
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                    & v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(X1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
                        ( ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5)
                          | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5)
                          | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                        & X0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK3),u1_struct_0(X3),u1_struct_0(sK3),X4,X6)
                            & X0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK3))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK2 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) )
    & ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) )
    & r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8)
    & sK2 = sK5
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f37,f44,f43,f42,f41,f40,f39,f38])).

fof(f82,plain,(
    r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    sK2 = sK5 ),
    inference(cnf_transformation,[],[f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f45])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3771,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_475,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | u1_struct_0(sK5) != X4
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK3) != X5
    | u1_struct_0(sK3) != X2
    | sK8 != X3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_476,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | sK8 = sK6 ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_478,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | sK8 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_28,c_27,c_26,c_22,c_21,c_20])).

cnf(c_3740,plain,
    ( sK8 = sK6
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3768,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3767,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3765,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6117,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3767,c_3765])).

cnf(c_8045,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3768,c_6117])).

cnf(c_3753,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3766,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4776,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3753,c_3766])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3770,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5405,plain,
    ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4776,c_3770])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3773,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6799,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5405,c_3773])).

cnf(c_8061,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8045,c_6799])).

cnf(c_9480,plain,
    ( sK8 = sK6
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3740,c_8061])).

cnf(c_10145,plain,
    ( sK8 = sK6
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3771,c_9480])).

cnf(c_3759,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( sK2 = sK5 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3820,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3759,c_19])).

cnf(c_4777,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_3766])).

cnf(c_5406,plain,
    ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4777,c_3770])).

cnf(c_6818,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5406,c_3773])).

cnf(c_8060,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8045,c_6818])).

cnf(c_9325,plain,
    ( sK8 = sK6
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3740,c_8060])).

cnf(c_9333,plain,
    ( sK8 = sK6
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3771,c_9325])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3769,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9397,plain,
    ( sK8 = X0
    | sK8 = sK6
    | r1_tarski(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9333,c_3769])).

cnf(c_10717,plain,
    ( sK8 = sK6 ),
    inference(superposition,[status(thm)],[c_10145,c_9397])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3750,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3800,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3750,c_19])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3748,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_3763,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3762,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3920,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_3763,c_3762])).

cnf(c_7216,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK8)
    | v1_funct_2(sK8,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_3920])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_43,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_44,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_55,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3758,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3809,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3758,c_19])).

cnf(c_7614,plain,
    ( v2_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK8)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7216,c_42,c_43,c_44,c_55,c_3809])).

cnf(c_7615,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK8)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7614])).

cnf(c_7626,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(sK4)) = k3_tmap_1(X0,sK3,sK2,sK4,sK8)
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3748,c_7615])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_3764,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5178,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK8,X0)
    | v1_funct_2(sK8,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_3764])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_40,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5628,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5178,c_39,c_40,c_41,c_42,c_43,c_44,c_55,c_3809])).

cnf(c_5629,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK8,X0)
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5628])).

cnf(c_5636,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK3,sK8,sK4) ),
    inference(superposition,[status(thm)],[c_3748,c_5629])).

cnf(c_7644,plain,
    ( k3_tmap_1(X0,sK3,sK2,sK4,sK8) = k2_tmap_1(sK2,sK3,sK8,sK4)
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7626,c_5636])).

cnf(c_8452,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,sK8) = k2_tmap_1(sK2,sK3,sK8,sK4)
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3800,c_7644])).

cnf(c_8765,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,sK8) = k2_tmap_1(sK2,sK3,sK8,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8452,c_39,c_40,c_41])).

cnf(c_17,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3760,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) = iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3865,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK8),sK7) = iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3760,c_19])).

cnf(c_8768,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK8,sK4),sK7) = iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8765,c_3865])).

cnf(c_10801,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10717,c_8768])).

cnf(c_16,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3761,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3870,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK8),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3761,c_19])).

cnf(c_8769,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK8,sK4),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8765,c_3870])).

cnf(c_10802,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10717,c_8769])).

cnf(c_10822,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10801,c_10802])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.08/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/0.99  
% 3.08/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.08/0.99  
% 3.08/0.99  ------  iProver source info
% 3.08/0.99  
% 3.08/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.08/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.08/0.99  git: non_committed_changes: false
% 3.08/0.99  git: last_make_outside_of_git: false
% 3.08/0.99  
% 3.08/0.99  ------ 
% 3.08/0.99  
% 3.08/0.99  ------ Input Options
% 3.08/0.99  
% 3.08/0.99  --out_options                           all
% 3.08/0.99  --tptp_safe_out                         true
% 3.08/0.99  --problem_path                          ""
% 3.08/0.99  --include_path                          ""
% 3.08/0.99  --clausifier                            res/vclausify_rel
% 3.08/0.99  --clausifier_options                    --mode clausify
% 3.08/0.99  --stdin                                 false
% 3.08/0.99  --stats_out                             all
% 3.08/0.99  
% 3.08/0.99  ------ General Options
% 3.08/0.99  
% 3.08/0.99  --fof                                   false
% 3.08/0.99  --time_out_real                         305.
% 3.08/0.99  --time_out_virtual                      -1.
% 3.08/0.99  --symbol_type_check                     false
% 3.08/0.99  --clausify_out                          false
% 3.08/0.99  --sig_cnt_out                           false
% 3.08/0.99  --trig_cnt_out                          false
% 3.08/0.99  --trig_cnt_out_tolerance                1.
% 3.08/0.99  --trig_cnt_out_sk_spl                   false
% 3.08/0.99  --abstr_cl_out                          false
% 3.08/0.99  
% 3.08/0.99  ------ Global Options
% 3.08/0.99  
% 3.08/0.99  --schedule                              default
% 3.08/0.99  --add_important_lit                     false
% 3.08/0.99  --prop_solver_per_cl                    1000
% 3.08/0.99  --min_unsat_core                        false
% 3.08/0.99  --soft_assumptions                      false
% 3.08/0.99  --soft_lemma_size                       3
% 3.08/0.99  --prop_impl_unit_size                   0
% 3.08/0.99  --prop_impl_unit                        []
% 3.08/0.99  --share_sel_clauses                     true
% 3.08/0.99  --reset_solvers                         false
% 3.08/0.99  --bc_imp_inh                            [conj_cone]
% 3.08/0.99  --conj_cone_tolerance                   3.
% 3.08/0.99  --extra_neg_conj                        none
% 3.08/0.99  --large_theory_mode                     true
% 3.08/0.99  --prolific_symb_bound                   200
% 3.08/0.99  --lt_threshold                          2000
% 3.08/0.99  --clause_weak_htbl                      true
% 3.08/0.99  --gc_record_bc_elim                     false
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing Options
% 3.08/0.99  
% 3.08/0.99  --preprocessing_flag                    true
% 3.08/0.99  --time_out_prep_mult                    0.1
% 3.08/0.99  --splitting_mode                        input
% 3.08/0.99  --splitting_grd                         true
% 3.08/0.99  --splitting_cvd                         false
% 3.08/0.99  --splitting_cvd_svl                     false
% 3.08/0.99  --splitting_nvd                         32
% 3.08/0.99  --sub_typing                            true
% 3.08/0.99  --prep_gs_sim                           true
% 3.08/0.99  --prep_unflatten                        true
% 3.08/0.99  --prep_res_sim                          true
% 3.08/0.99  --prep_upred                            true
% 3.08/0.99  --prep_sem_filter                       exhaustive
% 3.08/0.99  --prep_sem_filter_out                   false
% 3.08/0.99  --pred_elim                             true
% 3.08/0.99  --res_sim_input                         true
% 3.08/0.99  --eq_ax_congr_red                       true
% 3.08/0.99  --pure_diseq_elim                       true
% 3.08/0.99  --brand_transform                       false
% 3.08/0.99  --non_eq_to_eq                          false
% 3.08/0.99  --prep_def_merge                        true
% 3.08/0.99  --prep_def_merge_prop_impl              false
% 3.08/0.99  --prep_def_merge_mbd                    true
% 3.08/0.99  --prep_def_merge_tr_red                 false
% 3.08/0.99  --prep_def_merge_tr_cl                  false
% 3.08/0.99  --smt_preprocessing                     true
% 3.08/0.99  --smt_ac_axioms                         fast
% 3.08/0.99  --preprocessed_out                      false
% 3.08/0.99  --preprocessed_stats                    false
% 3.08/0.99  
% 3.08/0.99  ------ Abstraction refinement Options
% 3.08/0.99  
% 3.08/0.99  --abstr_ref                             []
% 3.08/0.99  --abstr_ref_prep                        false
% 3.08/0.99  --abstr_ref_until_sat                   false
% 3.08/0.99  --abstr_ref_sig_restrict                funpre
% 3.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/0.99  --abstr_ref_under                       []
% 3.08/0.99  
% 3.08/0.99  ------ SAT Options
% 3.08/0.99  
% 3.08/0.99  --sat_mode                              false
% 3.08/0.99  --sat_fm_restart_options                ""
% 3.08/0.99  --sat_gr_def                            false
% 3.08/0.99  --sat_epr_types                         true
% 3.08/0.99  --sat_non_cyclic_types                  false
% 3.08/0.99  --sat_finite_models                     false
% 3.08/0.99  --sat_fm_lemmas                         false
% 3.08/0.99  --sat_fm_prep                           false
% 3.08/0.99  --sat_fm_uc_incr                        true
% 3.08/0.99  --sat_out_model                         small
% 3.08/0.99  --sat_out_clauses                       false
% 3.08/0.99  
% 3.08/0.99  ------ QBF Options
% 3.08/0.99  
% 3.08/0.99  --qbf_mode                              false
% 3.08/0.99  --qbf_elim_univ                         false
% 3.08/0.99  --qbf_dom_inst                          none
% 3.08/0.99  --qbf_dom_pre_inst                      false
% 3.08/0.99  --qbf_sk_in                             false
% 3.08/0.99  --qbf_pred_elim                         true
% 3.08/0.99  --qbf_split                             512
% 3.08/0.99  
% 3.08/0.99  ------ BMC1 Options
% 3.08/0.99  
% 3.08/0.99  --bmc1_incremental                      false
% 3.08/0.99  --bmc1_axioms                           reachable_all
% 3.08/0.99  --bmc1_min_bound                        0
% 3.08/0.99  --bmc1_max_bound                        -1
% 3.08/0.99  --bmc1_max_bound_default                -1
% 3.08/0.99  --bmc1_symbol_reachability              true
% 3.08/0.99  --bmc1_property_lemmas                  false
% 3.08/0.99  --bmc1_k_induction                      false
% 3.08/0.99  --bmc1_non_equiv_states                 false
% 3.08/0.99  --bmc1_deadlock                         false
% 3.08/0.99  --bmc1_ucm                              false
% 3.08/0.99  --bmc1_add_unsat_core                   none
% 3.08/0.99  --bmc1_unsat_core_children              false
% 3.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/0.99  --bmc1_out_stat                         full
% 3.08/0.99  --bmc1_ground_init                      false
% 3.08/0.99  --bmc1_pre_inst_next_state              false
% 3.08/0.99  --bmc1_pre_inst_state                   false
% 3.08/0.99  --bmc1_pre_inst_reach_state             false
% 3.08/0.99  --bmc1_out_unsat_core                   false
% 3.08/0.99  --bmc1_aig_witness_out                  false
% 3.08/0.99  --bmc1_verbose                          false
% 3.08/0.99  --bmc1_dump_clauses_tptp                false
% 3.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.08/0.99  --bmc1_dump_file                        -
% 3.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.08/0.99  --bmc1_ucm_extend_mode                  1
% 3.08/0.99  --bmc1_ucm_init_mode                    2
% 3.08/0.99  --bmc1_ucm_cone_mode                    none
% 3.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.08/0.99  --bmc1_ucm_relax_model                  4
% 3.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/0.99  --bmc1_ucm_layered_model                none
% 3.08/0.99  --bmc1_ucm_max_lemma_size               10
% 3.08/0.99  
% 3.08/0.99  ------ AIG Options
% 3.08/0.99  
% 3.08/0.99  --aig_mode                              false
% 3.08/0.99  
% 3.08/0.99  ------ Instantiation Options
% 3.08/0.99  
% 3.08/0.99  --instantiation_flag                    true
% 3.08/0.99  --inst_sos_flag                         false
% 3.08/0.99  --inst_sos_phase                        true
% 3.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/0.99  --inst_lit_sel_side                     num_symb
% 3.08/0.99  --inst_solver_per_active                1400
% 3.08/0.99  --inst_solver_calls_frac                1.
% 3.08/0.99  --inst_passive_queue_type               priority_queues
% 3.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/0.99  --inst_passive_queues_freq              [25;2]
% 3.08/0.99  --inst_dismatching                      true
% 3.08/0.99  --inst_eager_unprocessed_to_passive     true
% 3.08/0.99  --inst_prop_sim_given                   true
% 3.08/0.99  --inst_prop_sim_new                     false
% 3.08/0.99  --inst_subs_new                         false
% 3.08/0.99  --inst_eq_res_simp                      false
% 3.08/0.99  --inst_subs_given                       false
% 3.08/0.99  --inst_orphan_elimination               true
% 3.08/0.99  --inst_learning_loop_flag               true
% 3.08/0.99  --inst_learning_start                   3000
% 3.08/0.99  --inst_learning_factor                  2
% 3.08/0.99  --inst_start_prop_sim_after_learn       3
% 3.08/0.99  --inst_sel_renew                        solver
% 3.08/0.99  --inst_lit_activity_flag                true
% 3.08/0.99  --inst_restr_to_given                   false
% 3.08/0.99  --inst_activity_threshold               500
% 3.08/0.99  --inst_out_proof                        true
% 3.08/0.99  
% 3.08/0.99  ------ Resolution Options
% 3.08/0.99  
% 3.08/0.99  --resolution_flag                       true
% 3.08/0.99  --res_lit_sel                           adaptive
% 3.08/0.99  --res_lit_sel_side                      none
% 3.08/0.99  --res_ordering                          kbo
% 3.08/0.99  --res_to_prop_solver                    active
% 3.08/0.99  --res_prop_simpl_new                    false
% 3.08/0.99  --res_prop_simpl_given                  true
% 3.08/0.99  --res_passive_queue_type                priority_queues
% 3.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/0.99  --res_passive_queues_freq               [15;5]
% 3.08/0.99  --res_forward_subs                      full
% 3.08/0.99  --res_backward_subs                     full
% 3.08/0.99  --res_forward_subs_resolution           true
% 3.08/0.99  --res_backward_subs_resolution          true
% 3.08/0.99  --res_orphan_elimination                true
% 3.08/0.99  --res_time_limit                        2.
% 3.08/0.99  --res_out_proof                         true
% 3.08/0.99  
% 3.08/0.99  ------ Superposition Options
% 3.08/0.99  
% 3.08/0.99  --superposition_flag                    true
% 3.08/0.99  --sup_passive_queue_type                priority_queues
% 3.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.08/0.99  --demod_completeness_check              fast
% 3.08/0.99  --demod_use_ground                      true
% 3.08/0.99  --sup_to_prop_solver                    passive
% 3.08/0.99  --sup_prop_simpl_new                    true
% 3.08/0.99  --sup_prop_simpl_given                  true
% 3.08/0.99  --sup_fun_splitting                     false
% 3.08/0.99  --sup_smt_interval                      50000
% 3.08/0.99  
% 3.08/0.99  ------ Superposition Simplification Setup
% 3.08/0.99  
% 3.08/0.99  --sup_indices_passive                   []
% 3.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_full_bw                           [BwDemod]
% 3.08/0.99  --sup_immed_triv                        [TrivRules]
% 3.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_immed_bw_main                     []
% 3.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.99  
% 3.08/0.99  ------ Combination Options
% 3.08/0.99  
% 3.08/0.99  --comb_res_mult                         3
% 3.08/0.99  --comb_sup_mult                         2
% 3.08/0.99  --comb_inst_mult                        10
% 3.08/0.99  
% 3.08/0.99  ------ Debug Options
% 3.08/0.99  
% 3.08/0.99  --dbg_backtrace                         false
% 3.08/0.99  --dbg_dump_prop_clauses                 false
% 3.08/0.99  --dbg_dump_prop_clauses_file            -
% 3.08/0.99  --dbg_out_stat                          false
% 3.08/0.99  ------ Parsing...
% 3.08/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.08/0.99  ------ Proving...
% 3.08/0.99  ------ Problem Properties 
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  clauses                                 36
% 3.08/0.99  conjectures                             22
% 3.08/0.99  EPR                                     19
% 3.08/0.99  Horn                                    30
% 3.08/0.99  unary                                   21
% 3.08/0.99  binary                                  9
% 3.08/0.99  lits                                    77
% 3.08/0.99  lits eq                                 5
% 3.08/0.99  fd_pure                                 0
% 3.08/0.99  fd_pseudo                               0
% 3.08/0.99  fd_cond                                 0
% 3.08/0.99  fd_pseudo_cond                          1
% 3.08/0.99  AC symbols                              0
% 3.08/0.99  
% 3.08/0.99  ------ Schedule dynamic 5 is on 
% 3.08/0.99  
% 3.08/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  ------ 
% 3.08/0.99  Current options:
% 3.08/0.99  ------ 
% 3.08/0.99  
% 3.08/0.99  ------ Input Options
% 3.08/0.99  
% 3.08/0.99  --out_options                           all
% 3.08/0.99  --tptp_safe_out                         true
% 3.08/0.99  --problem_path                          ""
% 3.08/0.99  --include_path                          ""
% 3.08/0.99  --clausifier                            res/vclausify_rel
% 3.08/0.99  --clausifier_options                    --mode clausify
% 3.08/0.99  --stdin                                 false
% 3.08/0.99  --stats_out                             all
% 3.08/0.99  
% 3.08/0.99  ------ General Options
% 3.08/0.99  
% 3.08/0.99  --fof                                   false
% 3.08/0.99  --time_out_real                         305.
% 3.08/0.99  --time_out_virtual                      -1.
% 3.08/0.99  --symbol_type_check                     false
% 3.08/0.99  --clausify_out                          false
% 3.08/0.99  --sig_cnt_out                           false
% 3.08/0.99  --trig_cnt_out                          false
% 3.08/0.99  --trig_cnt_out_tolerance                1.
% 3.08/0.99  --trig_cnt_out_sk_spl                   false
% 3.08/0.99  --abstr_cl_out                          false
% 3.08/0.99  
% 3.08/0.99  ------ Global Options
% 3.08/0.99  
% 3.08/0.99  --schedule                              default
% 3.08/0.99  --add_important_lit                     false
% 3.08/0.99  --prop_solver_per_cl                    1000
% 3.08/0.99  --min_unsat_core                        false
% 3.08/0.99  --soft_assumptions                      false
% 3.08/0.99  --soft_lemma_size                       3
% 3.08/0.99  --prop_impl_unit_size                   0
% 3.08/0.99  --prop_impl_unit                        []
% 3.08/0.99  --share_sel_clauses                     true
% 3.08/0.99  --reset_solvers                         false
% 3.08/0.99  --bc_imp_inh                            [conj_cone]
% 3.08/0.99  --conj_cone_tolerance                   3.
% 3.08/0.99  --extra_neg_conj                        none
% 3.08/0.99  --large_theory_mode                     true
% 3.08/0.99  --prolific_symb_bound                   200
% 3.08/0.99  --lt_threshold                          2000
% 3.08/0.99  --clause_weak_htbl                      true
% 3.08/0.99  --gc_record_bc_elim                     false
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing Options
% 3.08/0.99  
% 3.08/0.99  --preprocessing_flag                    true
% 3.08/0.99  --time_out_prep_mult                    0.1
% 3.08/0.99  --splitting_mode                        input
% 3.08/0.99  --splitting_grd                         true
% 3.08/0.99  --splitting_cvd                         false
% 3.08/0.99  --splitting_cvd_svl                     false
% 3.08/0.99  --splitting_nvd                         32
% 3.08/0.99  --sub_typing                            true
% 3.08/0.99  --prep_gs_sim                           true
% 3.08/0.99  --prep_unflatten                        true
% 3.08/0.99  --prep_res_sim                          true
% 3.08/0.99  --prep_upred                            true
% 3.08/0.99  --prep_sem_filter                       exhaustive
% 3.08/0.99  --prep_sem_filter_out                   false
% 3.08/0.99  --pred_elim                             true
% 3.08/0.99  --res_sim_input                         true
% 3.08/0.99  --eq_ax_congr_red                       true
% 3.08/0.99  --pure_diseq_elim                       true
% 3.08/0.99  --brand_transform                       false
% 3.08/0.99  --non_eq_to_eq                          false
% 3.08/0.99  --prep_def_merge                        true
% 3.08/0.99  --prep_def_merge_prop_impl              false
% 3.08/0.99  --prep_def_merge_mbd                    true
% 3.08/0.99  --prep_def_merge_tr_red                 false
% 3.08/0.99  --prep_def_merge_tr_cl                  false
% 3.08/0.99  --smt_preprocessing                     true
% 3.08/0.99  --smt_ac_axioms                         fast
% 3.08/0.99  --preprocessed_out                      false
% 3.08/0.99  --preprocessed_stats                    false
% 3.08/0.99  
% 3.08/0.99  ------ Abstraction refinement Options
% 3.08/0.99  
% 3.08/0.99  --abstr_ref                             []
% 3.08/0.99  --abstr_ref_prep                        false
% 3.08/0.99  --abstr_ref_until_sat                   false
% 3.08/0.99  --abstr_ref_sig_restrict                funpre
% 3.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/0.99  --abstr_ref_under                       []
% 3.08/0.99  
% 3.08/0.99  ------ SAT Options
% 3.08/0.99  
% 3.08/0.99  --sat_mode                              false
% 3.08/0.99  --sat_fm_restart_options                ""
% 3.08/0.99  --sat_gr_def                            false
% 3.08/0.99  --sat_epr_types                         true
% 3.08/0.99  --sat_non_cyclic_types                  false
% 3.08/0.99  --sat_finite_models                     false
% 3.08/0.99  --sat_fm_lemmas                         false
% 3.08/0.99  --sat_fm_prep                           false
% 3.08/0.99  --sat_fm_uc_incr                        true
% 3.08/0.99  --sat_out_model                         small
% 3.08/0.99  --sat_out_clauses                       false
% 3.08/0.99  
% 3.08/0.99  ------ QBF Options
% 3.08/0.99  
% 3.08/0.99  --qbf_mode                              false
% 3.08/0.99  --qbf_elim_univ                         false
% 3.08/0.99  --qbf_dom_inst                          none
% 3.08/0.99  --qbf_dom_pre_inst                      false
% 3.08/0.99  --qbf_sk_in                             false
% 3.08/0.99  --qbf_pred_elim                         true
% 3.08/0.99  --qbf_split                             512
% 3.08/0.99  
% 3.08/0.99  ------ BMC1 Options
% 3.08/0.99  
% 3.08/0.99  --bmc1_incremental                      false
% 3.08/0.99  --bmc1_axioms                           reachable_all
% 3.08/0.99  --bmc1_min_bound                        0
% 3.08/0.99  --bmc1_max_bound                        -1
% 3.08/0.99  --bmc1_max_bound_default                -1
% 3.08/0.99  --bmc1_symbol_reachability              true
% 3.08/0.99  --bmc1_property_lemmas                  false
% 3.08/0.99  --bmc1_k_induction                      false
% 3.08/0.99  --bmc1_non_equiv_states                 false
% 3.08/0.99  --bmc1_deadlock                         false
% 3.08/0.99  --bmc1_ucm                              false
% 3.08/0.99  --bmc1_add_unsat_core                   none
% 3.08/0.99  --bmc1_unsat_core_children              false
% 3.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/0.99  --bmc1_out_stat                         full
% 3.08/0.99  --bmc1_ground_init                      false
% 3.08/0.99  --bmc1_pre_inst_next_state              false
% 3.08/0.99  --bmc1_pre_inst_state                   false
% 3.08/0.99  --bmc1_pre_inst_reach_state             false
% 3.08/0.99  --bmc1_out_unsat_core                   false
% 3.08/0.99  --bmc1_aig_witness_out                  false
% 3.08/0.99  --bmc1_verbose                          false
% 3.08/0.99  --bmc1_dump_clauses_tptp                false
% 3.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.08/0.99  --bmc1_dump_file                        -
% 3.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.08/0.99  --bmc1_ucm_extend_mode                  1
% 3.08/0.99  --bmc1_ucm_init_mode                    2
% 3.08/0.99  --bmc1_ucm_cone_mode                    none
% 3.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.08/0.99  --bmc1_ucm_relax_model                  4
% 3.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/0.99  --bmc1_ucm_layered_model                none
% 3.08/0.99  --bmc1_ucm_max_lemma_size               10
% 3.08/0.99  
% 3.08/0.99  ------ AIG Options
% 3.08/0.99  
% 3.08/0.99  --aig_mode                              false
% 3.08/0.99  
% 3.08/0.99  ------ Instantiation Options
% 3.08/0.99  
% 3.08/0.99  --instantiation_flag                    true
% 3.08/0.99  --inst_sos_flag                         false
% 3.08/0.99  --inst_sos_phase                        true
% 3.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/0.99  --inst_lit_sel_side                     none
% 3.08/0.99  --inst_solver_per_active                1400
% 3.08/0.99  --inst_solver_calls_frac                1.
% 3.08/0.99  --inst_passive_queue_type               priority_queues
% 3.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/0.99  --inst_passive_queues_freq              [25;2]
% 3.08/0.99  --inst_dismatching                      true
% 3.08/0.99  --inst_eager_unprocessed_to_passive     true
% 3.08/0.99  --inst_prop_sim_given                   true
% 3.08/0.99  --inst_prop_sim_new                     false
% 3.08/0.99  --inst_subs_new                         false
% 3.08/0.99  --inst_eq_res_simp                      false
% 3.08/0.99  --inst_subs_given                       false
% 3.08/0.99  --inst_orphan_elimination               true
% 3.08/0.99  --inst_learning_loop_flag               true
% 3.08/0.99  --inst_learning_start                   3000
% 3.08/0.99  --inst_learning_factor                  2
% 3.08/0.99  --inst_start_prop_sim_after_learn       3
% 3.08/0.99  --inst_sel_renew                        solver
% 3.08/0.99  --inst_lit_activity_flag                true
% 3.08/0.99  --inst_restr_to_given                   false
% 3.08/0.99  --inst_activity_threshold               500
% 3.08/0.99  --inst_out_proof                        true
% 3.08/0.99  
% 3.08/0.99  ------ Resolution Options
% 3.08/0.99  
% 3.08/0.99  --resolution_flag                       false
% 3.08/0.99  --res_lit_sel                           adaptive
% 3.08/0.99  --res_lit_sel_side                      none
% 3.08/0.99  --res_ordering                          kbo
% 3.08/0.99  --res_to_prop_solver                    active
% 3.08/0.99  --res_prop_simpl_new                    false
% 3.08/0.99  --res_prop_simpl_given                  true
% 3.08/0.99  --res_passive_queue_type                priority_queues
% 3.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/0.99  --res_passive_queues_freq               [15;5]
% 3.08/0.99  --res_forward_subs                      full
% 3.08/0.99  --res_backward_subs                     full
% 3.08/0.99  --res_forward_subs_resolution           true
% 3.08/0.99  --res_backward_subs_resolution          true
% 3.08/0.99  --res_orphan_elimination                true
% 3.08/0.99  --res_time_limit                        2.
% 3.08/0.99  --res_out_proof                         true
% 3.08/0.99  
% 3.08/0.99  ------ Superposition Options
% 3.08/0.99  
% 3.08/0.99  --superposition_flag                    true
% 3.08/0.99  --sup_passive_queue_type                priority_queues
% 3.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.08/0.99  --demod_completeness_check              fast
% 3.08/0.99  --demod_use_ground                      true
% 3.08/0.99  --sup_to_prop_solver                    passive
% 3.08/0.99  --sup_prop_simpl_new                    true
% 3.08/0.99  --sup_prop_simpl_given                  true
% 3.08/0.99  --sup_fun_splitting                     false
% 3.08/0.99  --sup_smt_interval                      50000
% 3.08/0.99  
% 3.08/0.99  ------ Superposition Simplification Setup
% 3.08/0.99  
% 3.08/0.99  --sup_indices_passive                   []
% 3.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_full_bw                           [BwDemod]
% 3.08/0.99  --sup_immed_triv                        [TrivRules]
% 3.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_immed_bw_main                     []
% 3.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.99  
% 3.08/0.99  ------ Combination Options
% 3.08/0.99  
% 3.08/0.99  --comb_res_mult                         3
% 3.08/0.99  --comb_sup_mult                         2
% 3.08/0.99  --comb_inst_mult                        10
% 3.08/0.99  
% 3.08/0.99  ------ Debug Options
% 3.08/0.99  
% 3.08/0.99  --dbg_backtrace                         false
% 3.08/0.99  --dbg_dump_prop_clauses                 false
% 3.08/0.99  --dbg_dump_prop_clauses_file            -
% 3.08/0.99  --dbg_out_stat                          false
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  ------ Proving...
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  % SZS status Theorem for theBenchmark.p
% 3.08/0.99  
% 3.08/0.99   Resolution empty clause
% 3.08/0.99  
% 3.08/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.08/0.99  
% 3.08/0.99  fof(f2,axiom,(
% 3.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f12,plain,(
% 3.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.08/0.99    inference(ennf_transformation,[],[f2])).
% 3.08/0.99  
% 3.08/0.99  fof(f28,plain,(
% 3.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.08/0.99    inference(nnf_transformation,[],[f12])).
% 3.08/0.99  
% 3.08/0.99  fof(f29,plain,(
% 3.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.08/0.99    inference(rectify,[],[f28])).
% 3.08/0.99  
% 3.08/0.99  fof(f30,plain,(
% 3.08/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f31,plain,(
% 3.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.08/0.99  
% 3.08/0.99  fof(f49,plain,(
% 3.08/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f31])).
% 3.08/0.99  
% 3.08/0.99  fof(f6,axiom,(
% 3.08/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f14,plain,(
% 3.08/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.08/0.99    inference(ennf_transformation,[],[f6])).
% 3.08/0.99  
% 3.08/0.99  fof(f15,plain,(
% 3.08/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.08/0.99    inference(flattening,[],[f14])).
% 3.08/0.99  
% 3.08/0.99  fof(f35,plain,(
% 3.08/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.08/0.99    inference(nnf_transformation,[],[f15])).
% 3.08/0.99  
% 3.08/0.99  fof(f57,plain,(
% 3.08/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f35])).
% 3.08/0.99  
% 3.08/0.99  fof(f10,conjecture,(
% 3.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f11,negated_conjecture,(
% 3.08/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.08/0.99    inference(negated_conjecture,[],[f10])).
% 3.08/0.99  
% 3.08/0.99  fof(f22,plain,(
% 3.08/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.08/0.99    inference(ennf_transformation,[],[f11])).
% 3.08/0.99  
% 3.08/0.99  fof(f23,plain,(
% 3.08/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.08/0.99    inference(flattening,[],[f22])).
% 3.08/0.99  
% 3.08/0.99  fof(f36,plain,(
% 3.08/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.08/0.99    inference(nnf_transformation,[],[f23])).
% 3.08/0.99  
% 3.08/0.99  fof(f37,plain,(
% 3.08/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.08/0.99    inference(flattening,[],[f36])).
% 3.08/0.99  
% 3.08/0.99  fof(f44,plain,(
% 3.08/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK8) & X0 = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f43,plain,(
% 3.08/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f42,plain,(
% 3.08/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK6,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f41,plain,(
% 3.08/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK5),u1_struct_0(X1),X4,X6) & sK5 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f40,plain,(
% 3.08/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5)) & (r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f39,plain,(
% 3.08/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK3),u1_struct_0(X3),u1_struct_0(sK3),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f38,plain,(
% 3.08/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK2 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f45,plain,(
% 3.08/0.99    (((((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)) & (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)) & r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) & sK2 = sK5 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f37,f44,f43,f42,f41,f40,f39,f38])).
% 3.08/0.99  
% 3.08/0.99  fof(f82,plain,(
% 3.08/0.99    r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f72,plain,(
% 3.08/0.99    v1_funct_1(sK6)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f73,plain,(
% 3.08/0.99    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f74,plain,(
% 3.08/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f78,plain,(
% 3.08/0.99    v1_funct_1(sK8)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f79,plain,(
% 3.08/0.99    v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f80,plain,(
% 3.08/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f3,axiom,(
% 3.08/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f32,plain,(
% 3.08/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.08/0.99    inference(nnf_transformation,[],[f3])).
% 3.08/0.99  
% 3.08/0.99  fof(f33,plain,(
% 3.08/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.08/0.99    inference(flattening,[],[f32])).
% 3.08/0.99  
% 3.08/0.99  fof(f52,plain,(
% 3.08/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.08/0.99    inference(cnf_transformation,[],[f33])).
% 3.08/0.99  
% 3.08/0.99  fof(f85,plain,(
% 3.08/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.08/0.99    inference(equality_resolution,[],[f52])).
% 3.08/0.99  
% 3.08/0.99  fof(f4,axiom,(
% 3.08/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f34,plain,(
% 3.08/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.08/0.99    inference(nnf_transformation,[],[f4])).
% 3.08/0.99  
% 3.08/0.99  fof(f55,plain,(
% 3.08/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f34])).
% 3.08/0.99  
% 3.08/0.99  fof(f5,axiom,(
% 3.08/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f13,plain,(
% 3.08/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.08/0.99    inference(ennf_transformation,[],[f5])).
% 3.08/0.99  
% 3.08/0.99  fof(f56,plain,(
% 3.08/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f13])).
% 3.08/0.99  
% 3.08/0.99  fof(f54,plain,(
% 3.08/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.08/0.99    inference(cnf_transformation,[],[f34])).
% 3.08/0.99  
% 3.08/0.99  fof(f48,plain,(
% 3.08/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f31])).
% 3.08/0.99  
% 3.08/0.99  fof(f1,axiom,(
% 3.08/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f24,plain,(
% 3.08/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.08/0.99    inference(nnf_transformation,[],[f1])).
% 3.08/0.99  
% 3.08/0.99  fof(f25,plain,(
% 3.08/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.08/0.99    inference(rectify,[],[f24])).
% 3.08/0.99  
% 3.08/0.99  fof(f26,plain,(
% 3.08/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.08/0.99    introduced(choice_axiom,[])).
% 3.08/0.99  
% 3.08/0.99  fof(f27,plain,(
% 3.08/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.08/0.99  
% 3.08/0.99  fof(f46,plain,(
% 3.08/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f27])).
% 3.08/0.99  
% 3.08/0.99  fof(f81,plain,(
% 3.08/0.99    sK2 = sK5),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f53,plain,(
% 3.08/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f33])).
% 3.08/0.99  
% 3.08/0.99  fof(f71,plain,(
% 3.08/0.99    m1_pre_topc(sK5,sK2)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f69,plain,(
% 3.08/0.99    m1_pre_topc(sK4,sK2)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f8,axiom,(
% 3.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f18,plain,(
% 3.08/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.08/0.99    inference(ennf_transformation,[],[f8])).
% 3.08/0.99  
% 3.08/0.99  fof(f19,plain,(
% 3.08/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.08/0.99    inference(flattening,[],[f18])).
% 3.08/0.99  
% 3.08/0.99  fof(f60,plain,(
% 3.08/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f19])).
% 3.08/0.99  
% 3.08/0.99  fof(f9,axiom,(
% 3.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f20,plain,(
% 3.08/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.08/0.99    inference(ennf_transformation,[],[f9])).
% 3.08/0.99  
% 3.08/0.99  fof(f21,plain,(
% 3.08/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.08/0.99    inference(flattening,[],[f20])).
% 3.08/0.99  
% 3.08/0.99  fof(f61,plain,(
% 3.08/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f21])).
% 3.08/0.99  
% 3.08/0.99  fof(f65,plain,(
% 3.08/0.99    ~v2_struct_0(sK3)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f66,plain,(
% 3.08/0.99    v2_pre_topc(sK3)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f67,plain,(
% 3.08/0.99    l1_pre_topc(sK3)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f7,axiom,(
% 3.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.08/0.99  
% 3.08/0.99  fof(f16,plain,(
% 3.08/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.08/0.99    inference(ennf_transformation,[],[f7])).
% 3.08/0.99  
% 3.08/0.99  fof(f17,plain,(
% 3.08/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.08/0.99    inference(flattening,[],[f16])).
% 3.08/0.99  
% 3.08/0.99  fof(f59,plain,(
% 3.08/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.08/0.99    inference(cnf_transformation,[],[f17])).
% 3.08/0.99  
% 3.08/0.99  fof(f62,plain,(
% 3.08/0.99    ~v2_struct_0(sK2)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f63,plain,(
% 3.08/0.99    v2_pre_topc(sK2)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f64,plain,(
% 3.08/0.99    l1_pre_topc(sK2)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f83,plain,(
% 3.08/0.99    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  fof(f84,plain,(
% 3.08/0.99    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)),
% 3.08/0.99    inference(cnf_transformation,[],[f45])).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3,plain,
% 3.08/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.08/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3771,plain,
% 3.08/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.08/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_12,plain,
% 3.08/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.08/0.99      | ~ v1_funct_2(X5,X2,X3)
% 3.08/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.08/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.08/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/0.99      | ~ v1_funct_1(X5)
% 3.08/0.99      | ~ v1_funct_1(X4)
% 3.08/0.99      | v1_xboole_0(X1)
% 3.08/0.99      | v1_xboole_0(X3)
% 3.08/0.99      | X4 = X5 ),
% 3.08/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_18,negated_conjecture,
% 3.08/0.99      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
% 3.08/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_475,plain,
% 3.08/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.08/0.99      | ~ v1_funct_2(X3,X4,X5)
% 3.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.08/0.99      | ~ v1_funct_1(X0)
% 3.08/0.99      | ~ v1_funct_1(X3)
% 3.08/0.99      | v1_xboole_0(X2)
% 3.08/0.99      | v1_xboole_0(X5)
% 3.08/0.99      | X3 = X0
% 3.08/0.99      | u1_struct_0(sK5) != X4
% 3.08/0.99      | u1_struct_0(sK2) != X1
% 3.08/0.99      | u1_struct_0(sK3) != X5
% 3.08/0.99      | u1_struct_0(sK3) != X2
% 3.08/0.99      | sK8 != X3
% 3.08/0.99      | sK6 != X0 ),
% 3.08/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_476,plain,
% 3.08/0.99      ( ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.08/0.99      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.08/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.08/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.08/0.99      | ~ v1_funct_1(sK8)
% 3.08/0.99      | ~ v1_funct_1(sK6)
% 3.08/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.08/0.99      | sK8 = sK6 ),
% 3.08/0.99      inference(unflattening,[status(thm)],[c_475]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_28,negated_conjecture,
% 3.08/0.99      ( v1_funct_1(sK6) ),
% 3.08/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_27,negated_conjecture,
% 3.08/0.99      ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.08/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_26,negated_conjecture,
% 3.08/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.08/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_22,negated_conjecture,
% 3.08/0.99      ( v1_funct_1(sK8) ),
% 3.08/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_21,negated_conjecture,
% 3.08/0.99      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.08/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_20,negated_conjecture,
% 3.08/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.08/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_478,plain,
% 3.08/0.99      ( v1_xboole_0(u1_struct_0(sK3)) | sK8 = sK6 ),
% 3.08/0.99      inference(global_propositional_subsumption,
% 3.08/0.99                [status(thm)],
% 3.08/0.99                [c_476,c_28,c_27,c_26,c_22,c_21,c_20]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3740,plain,
% 3.08/0.99      ( sK8 = sK6 | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f85]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3768,plain,
% 3.08/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_8,plain,
% 3.08/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.08/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3767,plain,
% 3.08/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.08/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_10,plain,
% 3.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.99      | ~ v1_xboole_0(X2)
% 3.08/0.99      | v1_xboole_0(X0) ),
% 3.08/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3765,plain,
% 3.08/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.08/0.99      | v1_xboole_0(X2) != iProver_top
% 3.08/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_6117,plain,
% 3.08/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.08/0.99      | v1_xboole_0(X2) != iProver_top
% 3.08/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3767,c_3765]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_8045,plain,
% 3.08/0.99      ( v1_xboole_0(X0) != iProver_top
% 3.08/0.99      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3768,c_6117]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3753,plain,
% 3.08/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_9,plain,
% 3.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.08/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3766,plain,
% 3.08/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.08/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_4776,plain,
% 3.08/0.99      ( r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3753,c_3766]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_4,plain,
% 3.08/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.08/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3770,plain,
% 3.08/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.08/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.08/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_5405,plain,
% 3.08/0.99      ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top
% 3.08/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_4776,c_3770]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_1,plain,
% 3.08/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.08/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3773,plain,
% 3.08/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_6799,plain,
% 3.08/0.99      ( r2_hidden(X0,sK6) != iProver_top
% 3.08/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_5405,c_3773]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_8061,plain,
% 3.08/0.99      ( r2_hidden(X0,sK6) != iProver_top
% 3.08/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_8045,c_6799]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_9480,plain,
% 3.08/0.99      ( sK8 = sK6 | r2_hidden(X0,sK6) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3740,c_8061]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_10145,plain,
% 3.08/0.99      ( sK8 = sK6 | r1_tarski(sK6,X0) = iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3771,c_9480]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3759,plain,
% 3.08/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_19,negated_conjecture,
% 3.08/0.99      ( sK2 = sK5 ),
% 3.08/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3820,plain,
% 3.08/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.08/0.99      inference(light_normalisation,[status(thm)],[c_3759,c_19]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_4777,plain,
% 3.08/0.99      ( r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3820,c_3766]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_5406,plain,
% 3.08/0.99      ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top
% 3.08/0.99      | r2_hidden(X0,sK8) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_4777,c_3770]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_6818,plain,
% 3.08/0.99      ( r2_hidden(X0,sK8) != iProver_top
% 3.08/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_5406,c_3773]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_8060,plain,
% 3.08/0.99      ( r2_hidden(X0,sK8) != iProver_top
% 3.08/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_8045,c_6818]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_9325,plain,
% 3.08/0.99      ( sK8 = sK6 | r2_hidden(X0,sK8) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3740,c_8060]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_9333,plain,
% 3.08/0.99      ( sK8 = sK6 | r1_tarski(sK8,X0) = iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3771,c_9325]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_5,plain,
% 3.08/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.08/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3769,plain,
% 3.08/0.99      ( X0 = X1
% 3.08/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.08/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_9397,plain,
% 3.08/0.99      ( sK8 = X0 | sK8 = sK6 | r1_tarski(X0,sK8) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_9333,c_3769]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_10717,plain,
% 3.08/0.99      ( sK8 = sK6 ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_10145,c_9397]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_29,negated_conjecture,
% 3.08/0.99      ( m1_pre_topc(sK5,sK2) ),
% 3.08/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3750,plain,
% 3.08/0.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3800,plain,
% 3.08/0.99      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 3.08/0.99      inference(light_normalisation,[status(thm)],[c_3750,c_19]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_31,negated_conjecture,
% 3.08/0.99      ( m1_pre_topc(sK4,sK2) ),
% 3.08/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3748,plain,
% 3.08/0.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_14,plain,
% 3.08/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.08/0.99      | ~ m1_pre_topc(X3,X4)
% 3.08/0.99      | ~ m1_pre_topc(X3,X1)
% 3.08/0.99      | ~ m1_pre_topc(X1,X4)
% 3.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.08/0.99      | v2_struct_0(X4)
% 3.08/0.99      | v2_struct_0(X2)
% 3.08/0.99      | ~ v2_pre_topc(X2)
% 3.08/0.99      | ~ v2_pre_topc(X4)
% 3.08/0.99      | ~ l1_pre_topc(X2)
% 3.08/0.99      | ~ l1_pre_topc(X4)
% 3.08/0.99      | ~ v1_funct_1(X0)
% 3.08/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.08/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3763,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.08/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.08/0.99      | m1_pre_topc(X3,X4) != iProver_top
% 3.08/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.08/0.99      | m1_pre_topc(X0,X4) != iProver_top
% 3.08/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.08/0.99      | v2_struct_0(X4) = iProver_top
% 3.08/0.99      | v2_struct_0(X1) = iProver_top
% 3.08/0.99      | v2_pre_topc(X1) != iProver_top
% 3.08/0.99      | v2_pre_topc(X4) != iProver_top
% 3.08/0.99      | l1_pre_topc(X1) != iProver_top
% 3.08/0.99      | l1_pre_topc(X4) != iProver_top
% 3.08/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_15,plain,
% 3.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.08/0.99      | ~ m1_pre_topc(X1,X2)
% 3.08/0.99      | m1_pre_topc(X0,X2)
% 3.08/0.99      | ~ v2_pre_topc(X2)
% 3.08/0.99      | ~ l1_pre_topc(X2) ),
% 3.08/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3762,plain,
% 3.08/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.08/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 3.08/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 3.08/0.99      | v2_pre_topc(X2) != iProver_top
% 3.08/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3920,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.08/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.08/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.08/0.99      | m1_pre_topc(X0,X4) != iProver_top
% 3.08/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.08/0.99      | v2_struct_0(X4) = iProver_top
% 3.08/0.99      | v2_struct_0(X1) = iProver_top
% 3.08/0.99      | v2_pre_topc(X4) != iProver_top
% 3.08/0.99      | v2_pre_topc(X1) != iProver_top
% 3.08/0.99      | l1_pre_topc(X4) != iProver_top
% 3.08/0.99      | l1_pre_topc(X1) != iProver_top
% 3.08/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.08/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3763,c_3762]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_7216,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK8)
% 3.08/0.99      | v1_funct_2(sK8,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.08/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.08/0.99      | m1_pre_topc(sK2,X1) != iProver_top
% 3.08/0.99      | v2_struct_0(X1) = iProver_top
% 3.08/0.99      | v2_struct_0(sK3) = iProver_top
% 3.08/0.99      | v2_pre_topc(X1) != iProver_top
% 3.08/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.08/0.99      | l1_pre_topc(X1) != iProver_top
% 3.08/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.08/0.99      | v1_funct_1(sK8) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3820,c_3920]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_35,negated_conjecture,
% 3.08/0.99      ( ~ v2_struct_0(sK3) ),
% 3.08/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_42,plain,
% 3.08/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_34,negated_conjecture,
% 3.08/0.99      ( v2_pre_topc(sK3) ),
% 3.08/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_43,plain,
% 3.08/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_33,negated_conjecture,
% 3.08/0.99      ( l1_pre_topc(sK3) ),
% 3.08/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_44,plain,
% 3.08/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_55,plain,
% 3.08/0.99      ( v1_funct_1(sK8) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3758,plain,
% 3.08/0.99      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3809,plain,
% 3.08/0.99      ( v1_funct_2(sK8,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.08/0.99      inference(light_normalisation,[status(thm)],[c_3758,c_19]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_7614,plain,
% 3.08/0.99      ( v2_pre_topc(X1) != iProver_top
% 3.08/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK8)
% 3.08/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.08/0.99      | m1_pre_topc(sK2,X1) != iProver_top
% 3.08/0.99      | v2_struct_0(X1) = iProver_top
% 3.08/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.08/0.99      inference(global_propositional_subsumption,
% 3.08/0.99                [status(thm)],
% 3.08/0.99                [c_7216,c_42,c_43,c_44,c_55,c_3809]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_7615,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK8)
% 3.08/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.08/0.99      | m1_pre_topc(sK2,X1) != iProver_top
% 3.08/0.99      | v2_struct_0(X1) = iProver_top
% 3.08/0.99      | v2_pre_topc(X1) != iProver_top
% 3.08/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.08/0.99      inference(renaming,[status(thm)],[c_7614]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_7626,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(sK4)) = k3_tmap_1(X0,sK3,sK2,sK4,sK8)
% 3.08/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.08/0.99      | v2_struct_0(X0) = iProver_top
% 3.08/0.99      | v2_pre_topc(X0) != iProver_top
% 3.08/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3748,c_7615]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_13,plain,
% 3.08/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.08/0.99      | ~ m1_pre_topc(X3,X1)
% 3.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.08/0.99      | v2_struct_0(X1)
% 3.08/0.99      | v2_struct_0(X2)
% 3.08/0.99      | ~ v2_pre_topc(X2)
% 3.08/0.99      | ~ v2_pre_topc(X1)
% 3.08/0.99      | ~ l1_pre_topc(X2)
% 3.08/0.99      | ~ l1_pre_topc(X1)
% 3.08/0.99      | ~ v1_funct_1(X0)
% 3.08/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.08/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3764,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 3.08/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.08/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.08/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.08/0.99      | v2_struct_0(X1) = iProver_top
% 3.08/0.99      | v2_struct_0(X0) = iProver_top
% 3.08/0.99      | v2_pre_topc(X1) != iProver_top
% 3.08/0.99      | v2_pre_topc(X0) != iProver_top
% 3.08/0.99      | l1_pre_topc(X1) != iProver_top
% 3.08/0.99      | l1_pre_topc(X0) != iProver_top
% 3.08/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_5178,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK8,X0)
% 3.08/0.99      | v1_funct_2(sK8,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.08/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.08/0.99      | v2_struct_0(sK2) = iProver_top
% 3.08/0.99      | v2_struct_0(sK3) = iProver_top
% 3.08/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.08/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.08/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.08/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.08/0.99      | v1_funct_1(sK8) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3820,c_3764]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_38,negated_conjecture,
% 3.08/0.99      ( ~ v2_struct_0(sK2) ),
% 3.08/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_39,plain,
% 3.08/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_37,negated_conjecture,
% 3.08/0.99      ( v2_pre_topc(sK2) ),
% 3.08/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_40,plain,
% 3.08/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_36,negated_conjecture,
% 3.08/0.99      ( l1_pre_topc(sK2) ),
% 3.08/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_41,plain,
% 3.08/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_5628,plain,
% 3.08/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.08/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK8,X0) ),
% 3.08/0.99      inference(global_propositional_subsumption,
% 3.08/0.99                [status(thm)],
% 3.08/0.99                [c_5178,c_39,c_40,c_41,c_42,c_43,c_44,c_55,c_3809]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_5629,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK8,X0)
% 3.08/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.08/0.99      inference(renaming,[status(thm)],[c_5628]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_5636,plain,
% 3.08/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK8,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK3,sK8,sK4) ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3748,c_5629]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_7644,plain,
% 3.08/0.99      ( k3_tmap_1(X0,sK3,sK2,sK4,sK8) = k2_tmap_1(sK2,sK3,sK8,sK4)
% 3.08/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.08/0.99      | v2_struct_0(X0) = iProver_top
% 3.08/0.99      | v2_pre_topc(X0) != iProver_top
% 3.08/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.08/0.99      inference(light_normalisation,[status(thm)],[c_7626,c_5636]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_8452,plain,
% 3.08/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK4,sK8) = k2_tmap_1(sK2,sK3,sK8,sK4)
% 3.08/0.99      | v2_struct_0(sK2) = iProver_top
% 3.08/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.08/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.08/0.99      inference(superposition,[status(thm)],[c_3800,c_7644]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_8765,plain,
% 3.08/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK4,sK8) = k2_tmap_1(sK2,sK3,sK8,sK4) ),
% 3.08/0.99      inference(global_propositional_subsumption,
% 3.08/0.99                [status(thm)],
% 3.08/0.99                [c_8452,c_39,c_40,c_41]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_17,negated_conjecture,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
% 3.08/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
% 3.08/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3760,plain,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) = iProver_top
% 3.08/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3865,plain,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK8),sK7) = iProver_top
% 3.08/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
% 3.08/0.99      inference(light_normalisation,[status(thm)],[c_3760,c_19]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_8768,plain,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK8,sK4),sK7) = iProver_top
% 3.08/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
% 3.08/0.99      inference(demodulation,[status(thm)],[c_8765,c_3865]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_10801,plain,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
% 3.08/0.99      inference(demodulation,[status(thm)],[c_10717,c_8768]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_16,negated_conjecture,
% 3.08/0.99      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
% 3.08/0.99      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
% 3.08/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3761,plain,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) != iProver_top
% 3.08/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
% 3.08/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_3870,plain,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK8),sK7) != iProver_top
% 3.08/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
% 3.08/0.99      inference(light_normalisation,[status(thm)],[c_3761,c_19]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_8769,plain,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK8,sK4),sK7) != iProver_top
% 3.08/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
% 3.08/0.99      inference(demodulation,[status(thm)],[c_8765,c_3870]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_10802,plain,
% 3.08/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
% 3.08/0.99      inference(demodulation,[status(thm)],[c_10717,c_8769]) ).
% 3.08/0.99  
% 3.08/0.99  cnf(c_10822,plain,
% 3.08/0.99      ( $false ),
% 3.08/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_10801,c_10802]) ).
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.08/0.99  
% 3.08/0.99  ------                               Statistics
% 3.08/0.99  
% 3.08/0.99  ------ General
% 3.08/0.99  
% 3.08/0.99  abstr_ref_over_cycles:                  0
% 3.08/0.99  abstr_ref_under_cycles:                 0
% 3.08/0.99  gc_basic_clause_elim:                   0
% 3.08/0.99  forced_gc_time:                         0
% 3.08/0.99  parsing_time:                           0.012
% 3.08/0.99  unif_index_cands_time:                  0.
% 3.08/0.99  unif_index_add_time:                    0.
% 3.08/0.99  orderings_time:                         0.
% 3.08/0.99  out_proof_time:                         0.012
% 3.08/0.99  total_time:                             0.289
% 3.08/0.99  num_of_symbols:                         58
% 3.08/0.99  num_of_terms:                           6256
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing
% 3.08/0.99  
% 3.08/0.99  num_of_splits:                          0
% 3.08/0.99  num_of_split_atoms:                     0
% 3.08/0.99  num_of_reused_defs:                     0
% 3.08/0.99  num_eq_ax_congr_red:                    22
% 3.08/0.99  num_of_sem_filtered_clauses:            1
% 3.08/0.99  num_of_subtypes:                        0
% 3.08/0.99  monotx_restored_types:                  0
% 3.08/0.99  sat_num_of_epr_types:                   0
% 3.08/0.99  sat_num_of_non_cyclic_types:            0
% 3.08/0.99  sat_guarded_non_collapsed_types:        0
% 3.08/0.99  num_pure_diseq_elim:                    0
% 3.08/0.99  simp_replaced_by:                       0
% 3.08/0.99  res_preprocessed:                       183
% 3.08/0.99  prep_upred:                             0
% 3.08/0.99  prep_unflattend:                        66
% 3.08/0.99  smt_new_axioms:                         0
% 3.08/0.99  pred_elim_cands:                        11
% 3.08/0.99  pred_elim:                              1
% 3.08/0.99  pred_elim_cl:                           2
% 3.08/0.99  pred_elim_cycles:                       7
% 3.08/0.99  merged_defs:                            16
% 3.08/0.99  merged_defs_ncl:                        0
% 3.08/0.99  bin_hyper_res:                          16
% 3.08/0.99  prep_cycles:                            4
% 3.08/0.99  pred_elim_time:                         0.055
% 3.08/0.99  splitting_time:                         0.
% 3.08/0.99  sem_filter_time:                        0.
% 3.08/0.99  monotx_time:                            0.001
% 3.08/0.99  subtype_inf_time:                       0.
% 3.08/0.99  
% 3.08/0.99  ------ Problem properties
% 3.08/0.99  
% 3.08/0.99  clauses:                                36
% 3.08/0.99  conjectures:                            22
% 3.08/0.99  epr:                                    19
% 3.08/0.99  horn:                                   30
% 3.08/0.99  ground:                                 23
% 3.08/0.99  unary:                                  21
% 3.08/0.99  binary:                                 9
% 3.08/0.99  lits:                                   77
% 3.08/0.99  lits_eq:                                5
% 3.08/0.99  fd_pure:                                0
% 3.08/0.99  fd_pseudo:                              0
% 3.08/0.99  fd_cond:                                0
% 3.08/0.99  fd_pseudo_cond:                         1
% 3.08/0.99  ac_symbols:                             0
% 3.08/0.99  
% 3.08/0.99  ------ Propositional Solver
% 3.08/0.99  
% 3.08/0.99  prop_solver_calls:                      29
% 3.08/0.99  prop_fast_solver_calls:                 2218
% 3.08/0.99  smt_solver_calls:                       0
% 3.08/0.99  smt_fast_solver_calls:                  0
% 3.08/0.99  prop_num_of_clauses:                    3023
% 3.08/0.99  prop_preprocess_simplified:             8370
% 3.08/0.99  prop_fo_subsumed:                       129
% 3.08/0.99  prop_solver_time:                       0.
% 3.08/0.99  smt_solver_time:                        0.
% 3.08/0.99  smt_fast_solver_time:                   0.
% 3.08/0.99  prop_fast_solver_time:                  0.
% 3.08/0.99  prop_unsat_core_time:                   0.
% 3.08/0.99  
% 3.08/0.99  ------ QBF
% 3.08/0.99  
% 3.08/0.99  qbf_q_res:                              0
% 3.08/0.99  qbf_num_tautologies:                    0
% 3.08/0.99  qbf_prep_cycles:                        0
% 3.08/0.99  
% 3.08/0.99  ------ BMC1
% 3.08/0.99  
% 3.08/0.99  bmc1_current_bound:                     -1
% 3.08/0.99  bmc1_last_solved_bound:                 -1
% 3.08/0.99  bmc1_unsat_core_size:                   -1
% 3.08/0.99  bmc1_unsat_core_parents_size:           -1
% 3.08/0.99  bmc1_merge_next_fun:                    0
% 3.08/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.08/0.99  
% 3.08/0.99  ------ Instantiation
% 3.08/0.99  
% 3.08/0.99  inst_num_of_clauses:                    923
% 3.08/0.99  inst_num_in_passive:                    468
% 3.08/0.99  inst_num_in_active:                     467
% 3.08/0.99  inst_num_in_unprocessed:                0
% 3.08/0.99  inst_num_of_loops:                      560
% 3.08/0.99  inst_num_of_learning_restarts:          0
% 3.08/0.99  inst_num_moves_active_passive:          88
% 3.08/0.99  inst_lit_activity:                      0
% 3.08/0.99  inst_lit_activity_moves:                0
% 3.08/0.99  inst_num_tautologies:                   0
% 3.08/0.99  inst_num_prop_implied:                  0
% 3.08/0.99  inst_num_existing_simplified:           0
% 3.08/0.99  inst_num_eq_res_simplified:             0
% 3.08/0.99  inst_num_child_elim:                    0
% 3.08/0.99  inst_num_of_dismatching_blockings:      157
% 3.08/0.99  inst_num_of_non_proper_insts:           803
% 3.08/0.99  inst_num_of_duplicates:                 0
% 3.08/0.99  inst_inst_num_from_inst_to_res:         0
% 3.08/0.99  inst_dismatching_checking_time:         0.
% 3.08/0.99  
% 3.08/0.99  ------ Resolution
% 3.08/0.99  
% 3.08/0.99  res_num_of_clauses:                     0
% 3.08/0.99  res_num_in_passive:                     0
% 3.08/0.99  res_num_in_active:                      0
% 3.08/0.99  res_num_of_loops:                       187
% 3.08/0.99  res_forward_subset_subsumed:            168
% 3.08/0.99  res_backward_subset_subsumed:           28
% 3.08/0.99  res_forward_subsumed:                   0
% 3.08/0.99  res_backward_subsumed:                  0
% 3.08/0.99  res_forward_subsumption_resolution:     7
% 3.08/0.99  res_backward_subsumption_resolution:    0
% 3.08/0.99  res_clause_to_clause_subsumption:       325
% 3.08/0.99  res_orphan_elimination:                 0
% 3.08/0.99  res_tautology_del:                      80
% 3.08/0.99  res_num_eq_res_simplified:              0
% 3.08/0.99  res_num_sel_changes:                    0
% 3.08/0.99  res_moves_from_active_to_pass:          0
% 3.08/0.99  
% 3.08/0.99  ------ Superposition
% 3.08/0.99  
% 3.08/0.99  sup_time_total:                         0.
% 3.08/0.99  sup_time_generating:                    0.
% 3.08/0.99  sup_time_sim_full:                      0.
% 3.08/0.99  sup_time_sim_immed:                     0.
% 3.08/0.99  
% 3.08/0.99  sup_num_of_clauses:                     81
% 3.08/0.99  sup_num_in_active:                      67
% 3.08/0.99  sup_num_in_passive:                     14
% 3.08/0.99  sup_num_of_loops:                       111
% 3.08/0.99  sup_fw_superposition:                   96
% 3.08/0.99  sup_bw_superposition:                   54
% 3.08/0.99  sup_immediate_simplified:               25
% 3.08/0.99  sup_given_eliminated:                   0
% 3.08/0.99  comparisons_done:                       0
% 3.08/0.99  comparisons_avoided:                    15
% 3.08/0.99  
% 3.08/0.99  ------ Simplifications
% 3.08/0.99  
% 3.08/0.99  
% 3.08/0.99  sim_fw_subset_subsumed:                 9
% 3.08/0.99  sim_bw_subset_subsumed:                 17
% 3.08/0.99  sim_fw_subsumed:                        8
% 3.08/0.99  sim_bw_subsumed:                        0
% 3.08/0.99  sim_fw_subsumption_res:                 2
% 3.08/0.99  sim_bw_subsumption_res:                 0
% 3.08/0.99  sim_tautology_del:                      6
% 3.08/0.99  sim_eq_tautology_del:                   7
% 3.08/0.99  sim_eq_res_simp:                        0
% 3.08/0.99  sim_fw_demodulated:                     0
% 3.08/0.99  sim_bw_demodulated:                     32
% 3.08/0.99  sim_light_normalised:                   10
% 3.08/0.99  sim_joinable_taut:                      0
% 3.08/0.99  sim_joinable_simp:                      0
% 3.08/0.99  sim_ac_normalised:                      0
% 3.08/0.99  sim_smt_subsumption:                    0
% 3.08/0.99  
%------------------------------------------------------------------------------
