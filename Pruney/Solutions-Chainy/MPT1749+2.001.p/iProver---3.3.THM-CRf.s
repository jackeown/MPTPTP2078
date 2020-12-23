%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:20 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  223 (4248 expanded)
%              Number of clauses        :  142 (1026 expanded)
%              Number of leaves         :   20 (1601 expanded)
%              Depth                    :   23
%              Number of atoms          : 1002 (58616 expanded)
%              Number of equality atoms :  216 (4775 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3))
        & m1_subset_1(sK1(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3))
                & m1_subset_1(sK1(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK1(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & ! [X5] :
              ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
              | ~ r2_hidden(X5,u1_struct_0(X2))
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK6)
        & ! [X5] :
            ( k1_funct_1(sK6,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
            | ~ r2_hidden(X5,u1_struct_0(X2))
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
              & ! [X5] :
                  ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                  | ~ r2_hidden(X5,u1_struct_0(X2))
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK5,X2),X4)
            & ! [X5] :
                ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK5,X5)
                | ~ r2_hidden(X5,u1_struct_0(X2))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                  & ! [X5] :
                      ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                      | ~ r2_hidden(X5,u1_struct_0(X2))
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK4),X4)
                & ! [X5] :
                    ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                    | ~ r2_hidden(X5,u1_struct_0(sK4))
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK3,X0,X3,X2),X4)
                    & ! [X5] :
                        ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X3,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK3)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                            | ~ r2_hidden(X5,u1_struct_0(X2))
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X1,sK2,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK2),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK2))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)
    & ! [X5] :
        ( k1_funct_1(sK6,X5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK4))
        | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f42,f55,f54,f53,f52,f51])).

fof(f92,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
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
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f78,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X5)
      | ~ r2_hidden(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK1(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_812,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK1(X1,X3,X0),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK3,sK2,sK5,sK4) != X3
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK4) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_813,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | ~ v1_funct_1(sK6) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_815,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_813,c_24,c_23,c_22])).

cnf(c_816,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) ),
    inference(renaming,[status(thm)],[c_815])).

cnf(c_1776,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) ),
    inference(subtyping,[status(esa)],[c_816])).

cnf(c_2420,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_38,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_45,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_73,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_75,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_535,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_536,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_537,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_421,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_422,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_424,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_30])).

cnf(c_549,plain,
    ( l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_424])).

cnf(c_550,plain,
    ( l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_551,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_817,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1795,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_55,X2_56)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2797,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,X0_56))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_2858,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2797])).

cnf(c_2859,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2858])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1796,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_55,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2807,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,X0_56),u1_struct_0(X0_56),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_3070,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2807])).

cnf(c_3071,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3070])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1797,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_55,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2817,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_3310,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2817])).

cnf(c_3311,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3310])).

cnf(c_4296,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2420,c_38,c_44,c_45,c_46,c_75,c_537,c_551,c_817,c_2859,c_3071,c_3311])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1804,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | r2_hidden(X0_55,X1_55)
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2392,plain,
    ( m1_subset_1(X0_55,X1_55) != iProver_top
    | r2_hidden(X0_55,X1_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1804])).

cnf(c_4301,plain,
    ( r2_hidden(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4296,c_2392])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_562,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_563,plain,
    ( ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_564,plain,
    ( l1_struct_0(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_2737,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK4))
    | r2_hidden(X0_55,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_3660,plain,
    ( ~ m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
    | r2_hidden(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2737])).

cnf(c_3661,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3660])).

cnf(c_4838,plain,
    ( r2_hidden(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4301,c_38,c_44,c_45,c_46,c_75,c_537,c_551,c_564,c_817,c_2859,c_3071,c_3311,c_3661])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_410,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_411,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_413,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_30])).

cnf(c_1787,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_413])).

cnf(c_2409,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1787])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1803,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X0_55,X2_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2393,plain,
    ( m1_subset_1(X0_55,X1_55) = iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(X1_55)) != iProver_top
    | r2_hidden(X0_55,X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1803])).

cnf(c_3221,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0_55,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_2393])).

cnf(c_4843,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4838,c_3221])).

cnf(c_1790,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2406,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1790])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_432,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK3 != X1
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_433,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_437,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_32,c_31,c_30])).

cnf(c_438,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
    inference(renaming,[status(thm)],[c_437])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_501,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_438,c_34])).

cnf(c_502,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0,sK4) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_506,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_35,c_33])).

cnf(c_1785,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0_55,sK4) ),
    inference(subtyping,[status(esa)],[c_506])).

cnf(c_2411,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0_55,sK4)
    | v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_3776,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,sK5,sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2406,c_2411])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1799,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2397,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_3381,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2406,c_2397])).

cnf(c_2771,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_3721,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3381,c_27,c_25,c_2771])).

cnf(c_3777,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK4) = k7_relat_1(sK5,u1_struct_0(sK4))
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3776,c_3721])).

cnf(c_5066,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK4) = k7_relat_1(sK5,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3777,c_44,c_45])).

cnf(c_14458,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4843,c_5066])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1798,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ m1_subset_1(X3_55,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | v1_xboole_0(X1_55)
    | k3_funct_2(X1_55,X2_55,X0_55,X3_55) = k1_funct_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2398,plain,
    ( k3_funct_2(X0_55,X1_55,X2_55,X3_55) = k1_funct_1(X2_55,X3_55)
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | m1_subset_1(X3_55,X0_55) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1798])).

cnf(c_3462,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2406,c_2398])).

cnf(c_573,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_574,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_575,plain,
    ( l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_4594,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3462,c_44,c_45,c_537,c_575])).

cnf(c_14461,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) ),
    inference(superposition,[status(thm)],[c_14458,c_4594])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | k1_funct_1(sK6,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1794,negated_conjecture,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ r2_hidden(X0_55,u1_struct_0(sK4))
    | k1_funct_1(sK6,X0_55) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2402,plain,
    ( k1_funct_1(sK6,X0_55) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55)
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_55,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1794])).

cnf(c_14462,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK6,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
    | r2_hidden(sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14458,c_2402])).

cnf(c_14487,plain,
    ( k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK6,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
    | r2_hidden(sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14461,c_14462])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1800,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2396,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_2920,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2406,c_2396])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1801,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | ~ v1_relat_1(X2_55)
    | ~ v1_funct_1(X2_55)
    | k1_funct_1(k7_relat_1(X2_55,X1_55),X0_55) = k1_funct_1(X2_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2395,plain,
    ( k1_funct_1(k7_relat_1(X0_55,X1_55),X2_55) = k1_funct_1(X0_55,X2_55)
    | r2_hidden(X2_55,X1_55) != iProver_top
    | v1_relat_1(X0_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_4845,plain,
    ( k1_funct_1(k7_relat_1(X0_55,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) = k1_funct_1(X0_55,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6))
    | v1_relat_1(X0_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_4838,c_2395])).

cnf(c_8405,plain,
    ( k1_funct_1(k7_relat_1(X0_55,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(X0_55,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
    | v1_relat_1(X0_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4845,c_5066])).

cnf(c_8412,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2920,c_8405])).

cnf(c_2709,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1800])).

cnf(c_2710,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2709])).

cnf(c_8410,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8405])).

cnf(c_8544,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8412,c_44,c_46,c_2710,c_8410])).

cnf(c_7,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK1(X0,X2,X3)) != k1_funct_1(X2,sK1(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_832,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK3,sK2,sK5,sK4) != X3
    | k1_funct_1(X3,sK1(X1,X3,X0)) != k1_funct_1(X0,sK1(X1,X3,X0))
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK4) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_833,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | ~ v1_funct_1(sK6)
    | k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_835,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_833,c_24,c_23,c_22])).

cnf(c_836,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
    inference(renaming,[status(thm)],[c_835])).

cnf(c_1775,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
    inference(subtyping,[status(esa)],[c_836])).

cnf(c_2421,plain,
    ( k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6))
    | v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_74,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4304,plain,
    ( k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2421,c_33,c_27,c_26,c_25,c_74,c_536,c_550,c_1775,c_2858,c_3070,c_3310])).

cnf(c_5070,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) ),
    inference(demodulation,[status(thm)],[c_5066,c_4304])).

cnf(c_8547,plain,
    ( k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) ),
    inference(demodulation,[status(thm)],[c_8544,c_5070])).

cnf(c_5069,plain,
    ( r2_hidden(sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5066,c_4838])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14487,c_8547,c_5069])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.11/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.11/1.00  
% 4.11/1.00  ------  iProver source info
% 4.11/1.00  
% 4.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.11/1.00  git: non_committed_changes: false
% 4.11/1.00  git: last_make_outside_of_git: false
% 4.11/1.00  
% 4.11/1.00  ------ 
% 4.11/1.00  
% 4.11/1.00  ------ Input Options
% 4.11/1.00  
% 4.11/1.00  --out_options                           all
% 4.11/1.00  --tptp_safe_out                         true
% 4.11/1.00  --problem_path                          ""
% 4.11/1.00  --include_path                          ""
% 4.11/1.00  --clausifier                            res/vclausify_rel
% 4.11/1.00  --clausifier_options                    --mode clausify
% 4.11/1.00  --stdin                                 false
% 4.11/1.00  --stats_out                             all
% 4.11/1.00  
% 4.11/1.00  ------ General Options
% 4.11/1.00  
% 4.11/1.00  --fof                                   false
% 4.11/1.00  --time_out_real                         305.
% 4.11/1.00  --time_out_virtual                      -1.
% 4.11/1.00  --symbol_type_check                     false
% 4.11/1.00  --clausify_out                          false
% 4.11/1.00  --sig_cnt_out                           false
% 4.11/1.00  --trig_cnt_out                          false
% 4.11/1.00  --trig_cnt_out_tolerance                1.
% 4.11/1.00  --trig_cnt_out_sk_spl                   false
% 4.11/1.00  --abstr_cl_out                          false
% 4.11/1.00  
% 4.11/1.00  ------ Global Options
% 4.11/1.00  
% 4.11/1.00  --schedule                              default
% 4.11/1.00  --add_important_lit                     false
% 4.11/1.00  --prop_solver_per_cl                    1000
% 4.11/1.00  --min_unsat_core                        false
% 4.11/1.00  --soft_assumptions                      false
% 4.11/1.00  --soft_lemma_size                       3
% 4.11/1.00  --prop_impl_unit_size                   0
% 4.11/1.00  --prop_impl_unit                        []
% 4.11/1.00  --share_sel_clauses                     true
% 4.11/1.00  --reset_solvers                         false
% 4.11/1.00  --bc_imp_inh                            [conj_cone]
% 4.11/1.00  --conj_cone_tolerance                   3.
% 4.11/1.00  --extra_neg_conj                        none
% 4.11/1.00  --large_theory_mode                     true
% 4.11/1.00  --prolific_symb_bound                   200
% 4.11/1.00  --lt_threshold                          2000
% 4.11/1.00  --clause_weak_htbl                      true
% 4.11/1.00  --gc_record_bc_elim                     false
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing Options
% 4.11/1.00  
% 4.11/1.00  --preprocessing_flag                    true
% 4.11/1.00  --time_out_prep_mult                    0.1
% 4.11/1.00  --splitting_mode                        input
% 4.11/1.00  --splitting_grd                         true
% 4.11/1.00  --splitting_cvd                         false
% 4.11/1.00  --splitting_cvd_svl                     false
% 4.11/1.00  --splitting_nvd                         32
% 4.11/1.00  --sub_typing                            true
% 4.11/1.00  --prep_gs_sim                           true
% 4.11/1.00  --prep_unflatten                        true
% 4.11/1.00  --prep_res_sim                          true
% 4.11/1.00  --prep_upred                            true
% 4.11/1.00  --prep_sem_filter                       exhaustive
% 4.11/1.00  --prep_sem_filter_out                   false
% 4.11/1.00  --pred_elim                             true
% 4.11/1.00  --res_sim_input                         true
% 4.11/1.00  --eq_ax_congr_red                       true
% 4.11/1.00  --pure_diseq_elim                       true
% 4.11/1.00  --brand_transform                       false
% 4.11/1.00  --non_eq_to_eq                          false
% 4.11/1.00  --prep_def_merge                        true
% 4.11/1.00  --prep_def_merge_prop_impl              false
% 4.11/1.00  --prep_def_merge_mbd                    true
% 4.11/1.00  --prep_def_merge_tr_red                 false
% 4.11/1.00  --prep_def_merge_tr_cl                  false
% 4.11/1.00  --smt_preprocessing                     true
% 4.11/1.00  --smt_ac_axioms                         fast
% 4.11/1.00  --preprocessed_out                      false
% 4.11/1.00  --preprocessed_stats                    false
% 4.11/1.00  
% 4.11/1.00  ------ Abstraction refinement Options
% 4.11/1.00  
% 4.11/1.00  --abstr_ref                             []
% 4.11/1.00  --abstr_ref_prep                        false
% 4.11/1.00  --abstr_ref_until_sat                   false
% 4.11/1.00  --abstr_ref_sig_restrict                funpre
% 4.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/1.00  --abstr_ref_under                       []
% 4.11/1.00  
% 4.11/1.00  ------ SAT Options
% 4.11/1.00  
% 4.11/1.00  --sat_mode                              false
% 4.11/1.00  --sat_fm_restart_options                ""
% 4.11/1.00  --sat_gr_def                            false
% 4.11/1.00  --sat_epr_types                         true
% 4.11/1.00  --sat_non_cyclic_types                  false
% 4.11/1.00  --sat_finite_models                     false
% 4.11/1.00  --sat_fm_lemmas                         false
% 4.11/1.00  --sat_fm_prep                           false
% 4.11/1.00  --sat_fm_uc_incr                        true
% 4.11/1.00  --sat_out_model                         small
% 4.11/1.00  --sat_out_clauses                       false
% 4.11/1.00  
% 4.11/1.00  ------ QBF Options
% 4.11/1.00  
% 4.11/1.00  --qbf_mode                              false
% 4.11/1.00  --qbf_elim_univ                         false
% 4.11/1.00  --qbf_dom_inst                          none
% 4.11/1.00  --qbf_dom_pre_inst                      false
% 4.11/1.00  --qbf_sk_in                             false
% 4.11/1.00  --qbf_pred_elim                         true
% 4.11/1.00  --qbf_split                             512
% 4.11/1.00  
% 4.11/1.00  ------ BMC1 Options
% 4.11/1.00  
% 4.11/1.00  --bmc1_incremental                      false
% 4.11/1.00  --bmc1_axioms                           reachable_all
% 4.11/1.00  --bmc1_min_bound                        0
% 4.11/1.00  --bmc1_max_bound                        -1
% 4.11/1.00  --bmc1_max_bound_default                -1
% 4.11/1.00  --bmc1_symbol_reachability              true
% 4.11/1.00  --bmc1_property_lemmas                  false
% 4.11/1.00  --bmc1_k_induction                      false
% 4.11/1.00  --bmc1_non_equiv_states                 false
% 4.11/1.00  --bmc1_deadlock                         false
% 4.11/1.00  --bmc1_ucm                              false
% 4.11/1.00  --bmc1_add_unsat_core                   none
% 4.11/1.00  --bmc1_unsat_core_children              false
% 4.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/1.00  --bmc1_out_stat                         full
% 4.11/1.00  --bmc1_ground_init                      false
% 4.11/1.00  --bmc1_pre_inst_next_state              false
% 4.11/1.00  --bmc1_pre_inst_state                   false
% 4.11/1.00  --bmc1_pre_inst_reach_state             false
% 4.11/1.00  --bmc1_out_unsat_core                   false
% 4.11/1.00  --bmc1_aig_witness_out                  false
% 4.11/1.00  --bmc1_verbose                          false
% 4.11/1.00  --bmc1_dump_clauses_tptp                false
% 4.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.11/1.00  --bmc1_dump_file                        -
% 4.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.11/1.00  --bmc1_ucm_extend_mode                  1
% 4.11/1.00  --bmc1_ucm_init_mode                    2
% 4.11/1.00  --bmc1_ucm_cone_mode                    none
% 4.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.11/1.00  --bmc1_ucm_relax_model                  4
% 4.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/1.00  --bmc1_ucm_layered_model                none
% 4.11/1.00  --bmc1_ucm_max_lemma_size               10
% 4.11/1.00  
% 4.11/1.00  ------ AIG Options
% 4.11/1.00  
% 4.11/1.00  --aig_mode                              false
% 4.11/1.00  
% 4.11/1.00  ------ Instantiation Options
% 4.11/1.00  
% 4.11/1.00  --instantiation_flag                    true
% 4.11/1.00  --inst_sos_flag                         false
% 4.11/1.00  --inst_sos_phase                        true
% 4.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel_side                     num_symb
% 4.11/1.00  --inst_solver_per_active                1400
% 4.11/1.00  --inst_solver_calls_frac                1.
% 4.11/1.00  --inst_passive_queue_type               priority_queues
% 4.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/1.00  --inst_passive_queues_freq              [25;2]
% 4.11/1.00  --inst_dismatching                      true
% 4.11/1.00  --inst_eager_unprocessed_to_passive     true
% 4.11/1.00  --inst_prop_sim_given                   true
% 4.11/1.00  --inst_prop_sim_new                     false
% 4.11/1.00  --inst_subs_new                         false
% 4.11/1.00  --inst_eq_res_simp                      false
% 4.11/1.00  --inst_subs_given                       false
% 4.11/1.00  --inst_orphan_elimination               true
% 4.11/1.00  --inst_learning_loop_flag               true
% 4.11/1.00  --inst_learning_start                   3000
% 4.11/1.00  --inst_learning_factor                  2
% 4.11/1.00  --inst_start_prop_sim_after_learn       3
% 4.11/1.00  --inst_sel_renew                        solver
% 4.11/1.00  --inst_lit_activity_flag                true
% 4.11/1.00  --inst_restr_to_given                   false
% 4.11/1.00  --inst_activity_threshold               500
% 4.11/1.00  --inst_out_proof                        true
% 4.11/1.00  
% 4.11/1.00  ------ Resolution Options
% 4.11/1.00  
% 4.11/1.00  --resolution_flag                       true
% 4.11/1.00  --res_lit_sel                           adaptive
% 4.11/1.00  --res_lit_sel_side                      none
% 4.11/1.00  --res_ordering                          kbo
% 4.11/1.00  --res_to_prop_solver                    active
% 4.11/1.00  --res_prop_simpl_new                    false
% 4.11/1.00  --res_prop_simpl_given                  true
% 4.11/1.00  --res_passive_queue_type                priority_queues
% 4.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/1.00  --res_passive_queues_freq               [15;5]
% 4.11/1.00  --res_forward_subs                      full
% 4.11/1.00  --res_backward_subs                     full
% 4.11/1.00  --res_forward_subs_resolution           true
% 4.11/1.00  --res_backward_subs_resolution          true
% 4.11/1.00  --res_orphan_elimination                true
% 4.11/1.00  --res_time_limit                        2.
% 4.11/1.00  --res_out_proof                         true
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Options
% 4.11/1.00  
% 4.11/1.00  --superposition_flag                    true
% 4.11/1.00  --sup_passive_queue_type                priority_queues
% 4.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.11/1.00  --demod_completeness_check              fast
% 4.11/1.00  --demod_use_ground                      true
% 4.11/1.00  --sup_to_prop_solver                    passive
% 4.11/1.00  --sup_prop_simpl_new                    true
% 4.11/1.00  --sup_prop_simpl_given                  true
% 4.11/1.00  --sup_fun_splitting                     false
% 4.11/1.00  --sup_smt_interval                      50000
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Simplification Setup
% 4.11/1.00  
% 4.11/1.00  --sup_indices_passive                   []
% 4.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_full_bw                           [BwDemod]
% 4.11/1.00  --sup_immed_triv                        [TrivRules]
% 4.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_immed_bw_main                     []
% 4.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.00  
% 4.11/1.00  ------ Combination Options
% 4.11/1.00  
% 4.11/1.00  --comb_res_mult                         3
% 4.11/1.00  --comb_sup_mult                         2
% 4.11/1.00  --comb_inst_mult                        10
% 4.11/1.00  
% 4.11/1.00  ------ Debug Options
% 4.11/1.00  
% 4.11/1.00  --dbg_backtrace                         false
% 4.11/1.00  --dbg_dump_prop_clauses                 false
% 4.11/1.00  --dbg_dump_prop_clauses_file            -
% 4.11/1.00  --dbg_out_stat                          false
% 4.11/1.00  ------ Parsing...
% 4.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.11/1.00  ------ Proving...
% 4.11/1.00  ------ Problem Properties 
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  clauses                                 32
% 4.11/1.00  conjectures                             7
% 4.11/1.00  EPR                                     7
% 4.11/1.00  Horn                                    28
% 4.11/1.00  unary                                   13
% 4.11/1.00  binary                                  3
% 4.11/1.00  lits                                    99
% 4.11/1.00  lits eq                                 10
% 4.11/1.00  fd_pure                                 0
% 4.11/1.00  fd_pseudo                               0
% 4.11/1.00  fd_cond                                 0
% 4.11/1.00  fd_pseudo_cond                          0
% 4.11/1.00  AC symbols                              0
% 4.11/1.00  
% 4.11/1.00  ------ Schedule dynamic 5 is on 
% 4.11/1.00  
% 4.11/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  ------ 
% 4.11/1.00  Current options:
% 4.11/1.00  ------ 
% 4.11/1.00  
% 4.11/1.00  ------ Input Options
% 4.11/1.00  
% 4.11/1.00  --out_options                           all
% 4.11/1.00  --tptp_safe_out                         true
% 4.11/1.00  --problem_path                          ""
% 4.11/1.00  --include_path                          ""
% 4.11/1.00  --clausifier                            res/vclausify_rel
% 4.11/1.00  --clausifier_options                    --mode clausify
% 4.11/1.00  --stdin                                 false
% 4.11/1.00  --stats_out                             all
% 4.11/1.00  
% 4.11/1.00  ------ General Options
% 4.11/1.00  
% 4.11/1.00  --fof                                   false
% 4.11/1.00  --time_out_real                         305.
% 4.11/1.00  --time_out_virtual                      -1.
% 4.11/1.00  --symbol_type_check                     false
% 4.11/1.00  --clausify_out                          false
% 4.11/1.00  --sig_cnt_out                           false
% 4.11/1.00  --trig_cnt_out                          false
% 4.11/1.00  --trig_cnt_out_tolerance                1.
% 4.11/1.00  --trig_cnt_out_sk_spl                   false
% 4.11/1.00  --abstr_cl_out                          false
% 4.11/1.00  
% 4.11/1.00  ------ Global Options
% 4.11/1.00  
% 4.11/1.00  --schedule                              default
% 4.11/1.00  --add_important_lit                     false
% 4.11/1.00  --prop_solver_per_cl                    1000
% 4.11/1.00  --min_unsat_core                        false
% 4.11/1.00  --soft_assumptions                      false
% 4.11/1.00  --soft_lemma_size                       3
% 4.11/1.00  --prop_impl_unit_size                   0
% 4.11/1.00  --prop_impl_unit                        []
% 4.11/1.00  --share_sel_clauses                     true
% 4.11/1.00  --reset_solvers                         false
% 4.11/1.00  --bc_imp_inh                            [conj_cone]
% 4.11/1.00  --conj_cone_tolerance                   3.
% 4.11/1.00  --extra_neg_conj                        none
% 4.11/1.00  --large_theory_mode                     true
% 4.11/1.00  --prolific_symb_bound                   200
% 4.11/1.00  --lt_threshold                          2000
% 4.11/1.00  --clause_weak_htbl                      true
% 4.11/1.00  --gc_record_bc_elim                     false
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing Options
% 4.11/1.00  
% 4.11/1.00  --preprocessing_flag                    true
% 4.11/1.00  --time_out_prep_mult                    0.1
% 4.11/1.00  --splitting_mode                        input
% 4.11/1.00  --splitting_grd                         true
% 4.11/1.00  --splitting_cvd                         false
% 4.11/1.00  --splitting_cvd_svl                     false
% 4.11/1.00  --splitting_nvd                         32
% 4.11/1.00  --sub_typing                            true
% 4.11/1.00  --prep_gs_sim                           true
% 4.11/1.00  --prep_unflatten                        true
% 4.11/1.00  --prep_res_sim                          true
% 4.11/1.00  --prep_upred                            true
% 4.11/1.00  --prep_sem_filter                       exhaustive
% 4.11/1.00  --prep_sem_filter_out                   false
% 4.11/1.00  --pred_elim                             true
% 4.11/1.00  --res_sim_input                         true
% 4.11/1.00  --eq_ax_congr_red                       true
% 4.11/1.00  --pure_diseq_elim                       true
% 4.11/1.00  --brand_transform                       false
% 4.11/1.00  --non_eq_to_eq                          false
% 4.11/1.00  --prep_def_merge                        true
% 4.11/1.00  --prep_def_merge_prop_impl              false
% 4.11/1.00  --prep_def_merge_mbd                    true
% 4.11/1.00  --prep_def_merge_tr_red                 false
% 4.11/1.00  --prep_def_merge_tr_cl                  false
% 4.11/1.00  --smt_preprocessing                     true
% 4.11/1.00  --smt_ac_axioms                         fast
% 4.11/1.00  --preprocessed_out                      false
% 4.11/1.00  --preprocessed_stats                    false
% 4.11/1.00  
% 4.11/1.00  ------ Abstraction refinement Options
% 4.11/1.00  
% 4.11/1.00  --abstr_ref                             []
% 4.11/1.00  --abstr_ref_prep                        false
% 4.11/1.00  --abstr_ref_until_sat                   false
% 4.11/1.00  --abstr_ref_sig_restrict                funpre
% 4.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/1.00  --abstr_ref_under                       []
% 4.11/1.00  
% 4.11/1.00  ------ SAT Options
% 4.11/1.00  
% 4.11/1.00  --sat_mode                              false
% 4.11/1.00  --sat_fm_restart_options                ""
% 4.11/1.00  --sat_gr_def                            false
% 4.11/1.00  --sat_epr_types                         true
% 4.11/1.00  --sat_non_cyclic_types                  false
% 4.11/1.00  --sat_finite_models                     false
% 4.11/1.00  --sat_fm_lemmas                         false
% 4.11/1.00  --sat_fm_prep                           false
% 4.11/1.00  --sat_fm_uc_incr                        true
% 4.11/1.00  --sat_out_model                         small
% 4.11/1.00  --sat_out_clauses                       false
% 4.11/1.00  
% 4.11/1.00  ------ QBF Options
% 4.11/1.00  
% 4.11/1.00  --qbf_mode                              false
% 4.11/1.00  --qbf_elim_univ                         false
% 4.11/1.00  --qbf_dom_inst                          none
% 4.11/1.00  --qbf_dom_pre_inst                      false
% 4.11/1.00  --qbf_sk_in                             false
% 4.11/1.00  --qbf_pred_elim                         true
% 4.11/1.00  --qbf_split                             512
% 4.11/1.00  
% 4.11/1.00  ------ BMC1 Options
% 4.11/1.00  
% 4.11/1.00  --bmc1_incremental                      false
% 4.11/1.00  --bmc1_axioms                           reachable_all
% 4.11/1.00  --bmc1_min_bound                        0
% 4.11/1.00  --bmc1_max_bound                        -1
% 4.11/1.00  --bmc1_max_bound_default                -1
% 4.11/1.00  --bmc1_symbol_reachability              true
% 4.11/1.00  --bmc1_property_lemmas                  false
% 4.11/1.00  --bmc1_k_induction                      false
% 4.11/1.00  --bmc1_non_equiv_states                 false
% 4.11/1.00  --bmc1_deadlock                         false
% 4.11/1.00  --bmc1_ucm                              false
% 4.11/1.00  --bmc1_add_unsat_core                   none
% 4.11/1.00  --bmc1_unsat_core_children              false
% 4.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/1.00  --bmc1_out_stat                         full
% 4.11/1.00  --bmc1_ground_init                      false
% 4.11/1.00  --bmc1_pre_inst_next_state              false
% 4.11/1.00  --bmc1_pre_inst_state                   false
% 4.11/1.00  --bmc1_pre_inst_reach_state             false
% 4.11/1.00  --bmc1_out_unsat_core                   false
% 4.11/1.00  --bmc1_aig_witness_out                  false
% 4.11/1.00  --bmc1_verbose                          false
% 4.11/1.00  --bmc1_dump_clauses_tptp                false
% 4.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.11/1.00  --bmc1_dump_file                        -
% 4.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.11/1.00  --bmc1_ucm_extend_mode                  1
% 4.11/1.00  --bmc1_ucm_init_mode                    2
% 4.11/1.00  --bmc1_ucm_cone_mode                    none
% 4.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.11/1.00  --bmc1_ucm_relax_model                  4
% 4.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/1.00  --bmc1_ucm_layered_model                none
% 4.11/1.00  --bmc1_ucm_max_lemma_size               10
% 4.11/1.00  
% 4.11/1.00  ------ AIG Options
% 4.11/1.00  
% 4.11/1.00  --aig_mode                              false
% 4.11/1.00  
% 4.11/1.00  ------ Instantiation Options
% 4.11/1.00  
% 4.11/1.00  --instantiation_flag                    true
% 4.11/1.00  --inst_sos_flag                         false
% 4.11/1.00  --inst_sos_phase                        true
% 4.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel_side                     none
% 4.11/1.00  --inst_solver_per_active                1400
% 4.11/1.00  --inst_solver_calls_frac                1.
% 4.11/1.00  --inst_passive_queue_type               priority_queues
% 4.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/1.00  --inst_passive_queues_freq              [25;2]
% 4.11/1.00  --inst_dismatching                      true
% 4.11/1.00  --inst_eager_unprocessed_to_passive     true
% 4.11/1.00  --inst_prop_sim_given                   true
% 4.11/1.00  --inst_prop_sim_new                     false
% 4.11/1.00  --inst_subs_new                         false
% 4.11/1.00  --inst_eq_res_simp                      false
% 4.11/1.00  --inst_subs_given                       false
% 4.11/1.00  --inst_orphan_elimination               true
% 4.11/1.00  --inst_learning_loop_flag               true
% 4.11/1.00  --inst_learning_start                   3000
% 4.11/1.00  --inst_learning_factor                  2
% 4.11/1.00  --inst_start_prop_sim_after_learn       3
% 4.11/1.00  --inst_sel_renew                        solver
% 4.11/1.00  --inst_lit_activity_flag                true
% 4.11/1.00  --inst_restr_to_given                   false
% 4.11/1.00  --inst_activity_threshold               500
% 4.11/1.00  --inst_out_proof                        true
% 4.11/1.00  
% 4.11/1.00  ------ Resolution Options
% 4.11/1.00  
% 4.11/1.00  --resolution_flag                       false
% 4.11/1.00  --res_lit_sel                           adaptive
% 4.11/1.00  --res_lit_sel_side                      none
% 4.11/1.00  --res_ordering                          kbo
% 4.11/1.00  --res_to_prop_solver                    active
% 4.11/1.00  --res_prop_simpl_new                    false
% 4.11/1.00  --res_prop_simpl_given                  true
% 4.11/1.00  --res_passive_queue_type                priority_queues
% 4.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/1.00  --res_passive_queues_freq               [15;5]
% 4.11/1.00  --res_forward_subs                      full
% 4.11/1.00  --res_backward_subs                     full
% 4.11/1.00  --res_forward_subs_resolution           true
% 4.11/1.00  --res_backward_subs_resolution          true
% 4.11/1.00  --res_orphan_elimination                true
% 4.11/1.00  --res_time_limit                        2.
% 4.11/1.00  --res_out_proof                         true
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Options
% 4.11/1.00  
% 4.11/1.00  --superposition_flag                    true
% 4.11/1.00  --sup_passive_queue_type                priority_queues
% 4.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.11/1.00  --demod_completeness_check              fast
% 4.11/1.00  --demod_use_ground                      true
% 4.11/1.00  --sup_to_prop_solver                    passive
% 4.11/1.00  --sup_prop_simpl_new                    true
% 4.11/1.00  --sup_prop_simpl_given                  true
% 4.11/1.00  --sup_fun_splitting                     false
% 4.11/1.00  --sup_smt_interval                      50000
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Simplification Setup
% 4.11/1.00  
% 4.11/1.00  --sup_indices_passive                   []
% 4.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_full_bw                           [BwDemod]
% 4.11/1.00  --sup_immed_triv                        [TrivRules]
% 4.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_immed_bw_main                     []
% 4.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.00  
% 4.11/1.00  ------ Combination Options
% 4.11/1.00  
% 4.11/1.00  --comb_res_mult                         3
% 4.11/1.00  --comb_sup_mult                         2
% 4.11/1.00  --comb_inst_mult                        10
% 4.11/1.00  
% 4.11/1.00  ------ Debug Options
% 4.11/1.00  
% 4.11/1.00  --dbg_backtrace                         false
% 4.11/1.00  --dbg_dump_prop_clauses                 false
% 4.11/1.00  --dbg_dump_prop_clauses_file            -
% 4.11/1.00  --dbg_out_stat                          false
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  ------ Proving...
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  % SZS status Theorem for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  fof(f7,axiom,(
% 4.11/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f26,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.11/1.00    inference(ennf_transformation,[],[f7])).
% 4.11/1.00  
% 4.11/1.00  fof(f27,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.11/1.00    inference(flattening,[],[f26])).
% 4.11/1.00  
% 4.11/1.00  fof(f47,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.11/1.00    inference(nnf_transformation,[],[f27])).
% 4.11/1.00  
% 4.11/1.00  fof(f48,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.11/1.00    inference(rectify,[],[f47])).
% 4.11/1.00  
% 4.11/1.00  fof(f49,plain,(
% 4.11/1.00    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3)) & m1_subset_1(sK1(X0,X2,X3),X0)))),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f50,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3)) & m1_subset_1(sK1(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.11/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 4.11/1.00  
% 4.11/1.00  fof(f65,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK1(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f50])).
% 4.11/1.00  
% 4.11/1.00  fof(f16,conjecture,(
% 4.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f17,negated_conjecture,(
% 4.11/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 4.11/1.00    inference(negated_conjecture,[],[f16])).
% 4.11/1.00  
% 4.11/1.00  fof(f41,plain,(
% 4.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : ((k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f17])).
% 4.11/1.00  
% 4.11/1.00  fof(f42,plain,(
% 4.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.11/1.00    inference(flattening,[],[f41])).
% 4.11/1.00  
% 4.11/1.00  fof(f55,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK6) & ! [X5] : (k1_funct_1(sK6,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(sK6))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f54,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK5,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK5,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f53,plain,(
% 4.11/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK4),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f52,plain,(
% 4.11/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK3,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f51,plain,(
% 4.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X1,sK2,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK2),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f56,plain,(
% 4.11/1.00    ((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6) & ! [X5] : (k1_funct_1(sK6,X5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X5) | ~r2_hidden(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 4.11/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f42,f55,f54,f53,f52,f51])).
% 4.11/1.00  
% 4.11/1.00  fof(f92,plain,(
% 4.11/1.00    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f88,plain,(
% 4.11/1.00    v1_funct_1(sK6)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f89,plain,(
% 4.11/1.00    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2))),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f90,plain,(
% 4.11/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f79,plain,(
% 4.11/1.00    l1_pre_topc(sK2)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f85,plain,(
% 4.11/1.00    v1_funct_1(sK5)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f86,plain,(
% 4.11/1.00    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f87,plain,(
% 4.11/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f10,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f32,plain,(
% 4.11/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f10])).
% 4.11/1.00  
% 4.11/1.00  fof(f69,plain,(
% 4.11/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f32])).
% 4.11/1.00  
% 4.11/1.00  fof(f82,plain,(
% 4.11/1.00    l1_pre_topc(sK3)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f11,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f33,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f11])).
% 4.11/1.00  
% 4.11/1.00  fof(f70,plain,(
% 4.11/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f33])).
% 4.11/1.00  
% 4.11/1.00  fof(f84,plain,(
% 4.11/1.00    m1_pre_topc(sK4,sK3)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f14,axiom,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f38,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f14])).
% 4.11/1.00  
% 4.11/1.00  fof(f39,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 4.11/1.00    inference(flattening,[],[f38])).
% 4.11/1.00  
% 4.11/1.00  fof(f73,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f39])).
% 4.11/1.00  
% 4.11/1.00  fof(f74,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f39])).
% 4.11/1.00  
% 4.11/1.00  fof(f75,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f39])).
% 4.11/1.00  
% 4.11/1.00  fof(f2,axiom,(
% 4.11/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f18,plain,(
% 4.11/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 4.11/1.00    inference(ennf_transformation,[],[f2])).
% 4.11/1.00  
% 4.11/1.00  fof(f19,plain,(
% 4.11/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 4.11/1.00    inference(flattening,[],[f18])).
% 4.11/1.00  
% 4.11/1.00  fof(f59,plain,(
% 4.11/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f19])).
% 4.11/1.00  
% 4.11/1.00  fof(f12,axiom,(
% 4.11/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f34,plain,(
% 4.11/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f12])).
% 4.11/1.00  
% 4.11/1.00  fof(f35,plain,(
% 4.11/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 4.11/1.00    inference(flattening,[],[f34])).
% 4.11/1.00  
% 4.11/1.00  fof(f71,plain,(
% 4.11/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f35])).
% 4.11/1.00  
% 4.11/1.00  fof(f83,plain,(
% 4.11/1.00    ~v2_struct_0(sK4)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f15,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f40,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f15])).
% 4.11/1.00  
% 4.11/1.00  fof(f76,plain,(
% 4.11/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f40])).
% 4.11/1.00  
% 4.11/1.00  fof(f3,axiom,(
% 4.11/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f20,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 4.11/1.00    inference(ennf_transformation,[],[f3])).
% 4.11/1.00  
% 4.11/1.00  fof(f21,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.11/1.00    inference(flattening,[],[f20])).
% 4.11/1.00  
% 4.11/1.00  fof(f60,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f21])).
% 4.11/1.00  
% 4.11/1.00  fof(f13,axiom,(
% 4.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f36,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f13])).
% 4.11/1.00  
% 4.11/1.00  fof(f37,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.11/1.00    inference(flattening,[],[f36])).
% 4.11/1.00  
% 4.11/1.00  fof(f72,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f37])).
% 4.11/1.00  
% 4.11/1.00  fof(f80,plain,(
% 4.11/1.00    ~v2_struct_0(sK3)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f81,plain,(
% 4.11/1.00    v2_pre_topc(sK3)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f78,plain,(
% 4.11/1.00    v2_pre_topc(sK2)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f77,plain,(
% 4.11/1.00    ~v2_struct_0(sK2)),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f8,axiom,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f28,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.11/1.00    inference(ennf_transformation,[],[f8])).
% 4.11/1.00  
% 4.11/1.00  fof(f29,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.11/1.00    inference(flattening,[],[f28])).
% 4.11/1.00  
% 4.11/1.00  fof(f67,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f29])).
% 4.11/1.00  
% 4.11/1.00  fof(f9,axiom,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f30,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f9])).
% 4.11/1.00  
% 4.11/1.00  fof(f31,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 4.11/1.00    inference(flattening,[],[f30])).
% 4.11/1.00  
% 4.11/1.00  fof(f68,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f31])).
% 4.11/1.00  
% 4.11/1.00  fof(f91,plain,(
% 4.11/1.00    ( ! [X5] : (k1_funct_1(sK6,X5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X5) | ~r2_hidden(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 4.11/1.00    inference(cnf_transformation,[],[f56])).
% 4.11/1.00  
% 4.11/1.00  fof(f6,axiom,(
% 4.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f25,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/1.00    inference(ennf_transformation,[],[f6])).
% 4.11/1.00  
% 4.11/1.00  fof(f63,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.11/1.00    inference(cnf_transformation,[],[f25])).
% 4.11/1.00  
% 4.11/1.00  fof(f5,axiom,(
% 4.11/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f23,plain,(
% 4.11/1.00    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.11/1.00    inference(ennf_transformation,[],[f5])).
% 4.11/1.00  
% 4.11/1.00  fof(f24,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.11/1.00    inference(flattening,[],[f23])).
% 4.11/1.00  
% 4.11/1.00  fof(f62,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f24])).
% 4.11/1.00  
% 4.11/1.00  fof(f66,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f50])).
% 4.11/1.00  
% 4.11/1.00  cnf(c_8,plain,
% 4.11/1.00      ( r2_funct_2(X0,X1,X2,X3)
% 4.11/1.00      | ~ v1_funct_2(X3,X0,X1)
% 4.11/1.00      | ~ v1_funct_2(X2,X0,X1)
% 4.11/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.11/1.00      | m1_subset_1(sK1(X0,X2,X3),X0)
% 4.11/1.00      | ~ v1_funct_1(X2)
% 4.11/1.00      | ~ v1_funct_1(X3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f65]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_20,negated_conjecture,
% 4.11/1.00      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6) ),
% 4.11/1.00      inference(cnf_transformation,[],[f92]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_812,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/1.00      | ~ v1_funct_2(X3,X1,X2)
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | m1_subset_1(sK1(X1,X3,X0),X1)
% 4.11/1.00      | ~ v1_funct_1(X3)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_tmap_1(sK3,sK2,sK5,sK4) != X3
% 4.11/1.00      | u1_struct_0(sK2) != X2
% 4.11/1.00      | u1_struct_0(sK4) != X1
% 4.11/1.00      | sK6 != X0 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_813,plain,
% 4.11/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
% 4.11/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
% 4.11/1.00      | ~ v1_funct_1(sK6) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_812]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_24,negated_conjecture,
% 4.11/1.00      ( v1_funct_1(sK6) ),
% 4.11/1.00      inference(cnf_transformation,[],[f88]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_23,negated_conjecture,
% 4.11/1.00      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f89]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_22,negated_conjecture,
% 4.11/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 4.11/1.00      inference(cnf_transformation,[],[f90]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_815,plain,
% 4.11/1.00      ( ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
% 4.11/1.00      | ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_813,c_24,c_23,c_22]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_816,plain,
% 4.11/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
% 4.11/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_815]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1776,plain,
% 4.11/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
% 4.11/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_816]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2420,plain,
% 4.11/1.00      ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 4.11/1.00      | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top
% 4.11/1.00      | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_33,negated_conjecture,
% 4.11/1.00      ( l1_pre_topc(sK2) ),
% 4.11/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_38,plain,
% 4.11/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_27,negated_conjecture,
% 4.11/1.00      ( v1_funct_1(sK5) ),
% 4.11/1.00      inference(cnf_transformation,[],[f85]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_44,plain,
% 4.11/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_26,negated_conjecture,
% 4.11/1.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f86]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_45,plain,
% 4.11/1.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_25,negated_conjecture,
% 4.11/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 4.11/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_46,plain,
% 4.11/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_12,plain,
% 4.11/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f69]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_73,plain,
% 4.11/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_75,plain,
% 4.11/1.00      ( l1_pre_topc(sK2) != iProver_top
% 4.11/1.00      | l1_struct_0(sK2) = iProver_top ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_73]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_30,negated_conjecture,
% 4.11/1.00      ( l1_pre_topc(sK3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_535,plain,
% 4.11/1.00      ( l1_struct_0(X0) | sK3 != X0 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_536,plain,
% 4.11/1.00      ( l1_struct_0(sK3) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_535]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_537,plain,
% 4.11/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_13,plain,
% 4.11/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f70]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_28,negated_conjecture,
% 4.11/1.00      ( m1_pre_topc(sK4,sK3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_421,plain,
% 4.11/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK4 != X1 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_422,plain,
% 4.11/1.00      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK4) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_424,plain,
% 4.11/1.00      ( l1_pre_topc(sK4) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_422,c_30]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_549,plain,
% 4.11/1.00      ( l1_struct_0(X0) | sK4 != X0 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_424]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_550,plain,
% 4.11/1.00      ( l1_struct_0(sK4) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_549]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_551,plain,
% 4.11/1.00      ( l1_struct_0(sK4) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_817,plain,
% 4.11/1.00      ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 4.11/1.00      | m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top
% 4.11/1.00      | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_18,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.11/1.00      | ~ l1_struct_0(X1)
% 4.11/1.00      | ~ l1_struct_0(X3)
% 4.11/1.00      | ~ l1_struct_0(X2)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f73]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1795,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 4.11/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 4.11/1.00      | ~ l1_struct_0(X1_56)
% 4.11/1.00      | ~ l1_struct_0(X2_56)
% 4.11/1.00      | ~ l1_struct_0(X0_56)
% 4.11/1.00      | ~ v1_funct_1(X0_55)
% 4.11/1.00      | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_55,X2_56)) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2797,plain,
% 4.11/1.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ l1_struct_0(X0_56)
% 4.11/1.00      | ~ l1_struct_0(sK3)
% 4.11/1.00      | ~ l1_struct_0(sK2)
% 4.11/1.00      | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,X0_56))
% 4.11/1.00      | ~ v1_funct_1(sK5) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1795]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2858,plain,
% 4.11/1.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ l1_struct_0(sK3)
% 4.11/1.00      | ~ l1_struct_0(sK2)
% 4.11/1.00      | ~ l1_struct_0(sK4)
% 4.11/1.00      | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
% 4.11/1.00      | ~ v1_funct_1(sK5) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_2797]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2859,plain,
% 4.11/1.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 4.11/1.00      | l1_struct_0(sK3) != iProver_top
% 4.11/1.00      | l1_struct_0(sK2) != iProver_top
% 4.11/1.00      | l1_struct_0(sK4) != iProver_top
% 4.11/1.00      | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) = iProver_top
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_2858]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_17,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.11/1.00      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.11/1.00      | ~ l1_struct_0(X1)
% 4.11/1.00      | ~ l1_struct_0(X3)
% 4.11/1.00      | ~ l1_struct_0(X2)
% 4.11/1.00      | ~ v1_funct_1(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f74]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1796,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 4.11/1.00      | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_55,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
% 4.11/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 4.11/1.00      | ~ l1_struct_0(X1_56)
% 4.11/1.00      | ~ l1_struct_0(X2_56)
% 4.11/1.00      | ~ l1_struct_0(X0_56)
% 4.11/1.00      | ~ v1_funct_1(X0_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2807,plain,
% 4.11/1.00      ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,X0_56),u1_struct_0(X0_56),u1_struct_0(sK2))
% 4.11/1.00      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ l1_struct_0(X0_56)
% 4.11/1.00      | ~ l1_struct_0(sK3)
% 4.11/1.00      | ~ l1_struct_0(sK2)
% 4.11/1.00      | ~ v1_funct_1(sK5) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1796]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3070,plain,
% 4.11/1.00      ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ l1_struct_0(sK3)
% 4.11/1.00      | ~ l1_struct_0(sK2)
% 4.11/1.00      | ~ l1_struct_0(sK4)
% 4.11/1.00      | ~ v1_funct_1(sK5) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_2807]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3071,plain,
% 4.11/1.00      ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top
% 4.11/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 4.11/1.00      | l1_struct_0(sK3) != iProver_top
% 4.11/1.00      | l1_struct_0(sK2) != iProver_top
% 4.11/1.00      | l1_struct_0(sK4) != iProver_top
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_3070]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_16,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.11/1.00      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 4.11/1.00      | ~ l1_struct_0(X1)
% 4.11/1.00      | ~ l1_struct_0(X3)
% 4.11/1.00      | ~ l1_struct_0(X2)
% 4.11/1.00      | ~ v1_funct_1(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f75]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1797,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 4.11/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 4.11/1.00      | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_55,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 4.11/1.00      | ~ l1_struct_0(X1_56)
% 4.11/1.00      | ~ l1_struct_0(X2_56)
% 4.11/1.00      | ~ l1_struct_0(X0_56)
% 4.11/1.00      | ~ v1_funct_1(X0_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2817,plain,
% 4.11/1.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK2))))
% 4.11/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ l1_struct_0(X0_56)
% 4.11/1.00      | ~ l1_struct_0(sK3)
% 4.11/1.00      | ~ l1_struct_0(sK2)
% 4.11/1.00      | ~ v1_funct_1(sK5) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1797]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3310,plain,
% 4.11/1.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ l1_struct_0(sK3)
% 4.11/1.00      | ~ l1_struct_0(sK2)
% 4.11/1.00      | ~ l1_struct_0(sK4)
% 4.11/1.00      | ~ v1_funct_1(sK5) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_2817]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3311,plain,
% 4.11/1.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top
% 4.11/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 4.11/1.00      | l1_struct_0(sK3) != iProver_top
% 4.11/1.00      | l1_struct_0(sK2) != iProver_top
% 4.11/1.00      | l1_struct_0(sK4) != iProver_top
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_3310]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4296,plain,
% 4.11/1.00      ( m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2420,c_38,c_44,c_45,c_46,c_75,c_537,c_551,c_817,
% 4.11/1.00                 c_2859,c_3071,c_3311]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1804,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0_55,X1_55)
% 4.11/1.00      | r2_hidden(X0_55,X1_55)
% 4.11/1.00      | v1_xboole_0(X1_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2392,plain,
% 4.11/1.00      ( m1_subset_1(X0_55,X1_55) != iProver_top
% 4.11/1.00      | r2_hidden(X0_55,X1_55) = iProver_top
% 4.11/1.00      | v1_xboole_0(X1_55) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1804]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4301,plain,
% 4.11/1.00      ( r2_hidden(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top
% 4.11/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4296,c_2392]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_14,plain,
% 4.11/1.00      ( v2_struct_0(X0)
% 4.11/1.00      | ~ l1_struct_0(X0)
% 4.11/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f71]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_29,negated_conjecture,
% 4.11/1.00      ( ~ v2_struct_0(sK4) ),
% 4.11/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_562,plain,
% 4.11/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK4 != X0 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_563,plain,
% 4.11/1.00      ( ~ l1_struct_0(sK4) | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_562]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_564,plain,
% 4.11/1.00      ( l1_struct_0(sK4) != iProver_top
% 4.11/1.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2737,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK4))
% 4.11/1.00      | r2_hidden(X0_55,u1_struct_0(sK4))
% 4.11/1.00      | v1_xboole_0(u1_struct_0(sK4)) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1804]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3660,plain,
% 4.11/1.00      ( ~ m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
% 4.11/1.00      | r2_hidden(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4))
% 4.11/1.00      | v1_xboole_0(u1_struct_0(sK4)) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_2737]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3661,plain,
% 4.11/1.00      ( m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) != iProver_top
% 4.11/1.00      | r2_hidden(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top
% 4.11/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_3660]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4838,plain,
% 4.11/1.00      ( r2_hidden(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK4)) = iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_4301,c_38,c_44,c_45,c_46,c_75,c_537,c_551,c_564,c_817,
% 4.11/1.00                 c_2859,c_3071,c_3311,c_3661]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_19,plain,
% 4.11/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.11/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.11/1.00      | ~ l1_pre_topc(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_410,plain,
% 4.11/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | sK3 != X1
% 4.11/1.00      | sK4 != X0 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_411,plain,
% 4.11/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.11/1.00      | ~ l1_pre_topc(sK3) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_410]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_413,plain,
% 4.11/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_411,c_30]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1787,plain,
% 4.11/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_413]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2409,plain,
% 4.11/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1787]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3,plain,
% 4.11/1.00      ( m1_subset_1(X0,X1)
% 4.11/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.11/1.00      | ~ r2_hidden(X0,X2) ),
% 4.11/1.00      inference(cnf_transformation,[],[f60]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1803,plain,
% 4.11/1.00      ( m1_subset_1(X0_55,X1_55)
% 4.11/1.00      | ~ m1_subset_1(X2_55,k1_zfmisc_1(X1_55))
% 4.11/1.00      | ~ r2_hidden(X0_55,X2_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2393,plain,
% 4.11/1.00      ( m1_subset_1(X0_55,X1_55) = iProver_top
% 4.11/1.00      | m1_subset_1(X2_55,k1_zfmisc_1(X1_55)) != iProver_top
% 4.11/1.00      | r2_hidden(X0_55,X2_55) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1803]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3221,plain,
% 4.11/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK3)) = iProver_top
% 4.11/1.00      | r2_hidden(X0_55,u1_struct_0(sK4)) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_2409,c_2393]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4843,plain,
% 4.11/1.00      ( m1_subset_1(sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6),u1_struct_0(sK3)) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4838,c_3221]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1790,negated_conjecture,
% 4.11/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2406,plain,
% 4.11/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1790]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_15,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.11/1.00      | ~ m1_pre_topc(X3,X1)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.11/1.00      | ~ v2_pre_topc(X2)
% 4.11/1.00      | ~ v2_pre_topc(X1)
% 4.11/1.00      | v2_struct_0(X1)
% 4.11/1.00      | v2_struct_0(X2)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ l1_pre_topc(X2)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f72]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_432,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.11/1.00      | ~ v2_pre_topc(X2)
% 4.11/1.00      | ~ v2_pre_topc(X1)
% 4.11/1.00      | v2_struct_0(X2)
% 4.11/1.00      | v2_struct_0(X1)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ l1_pre_topc(X2)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 4.11/1.00      | sK3 != X1
% 4.11/1.00      | sK4 != X3 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_433,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 4.11/1.00      | ~ v2_pre_topc(X1)
% 4.11/1.00      | ~ v2_pre_topc(sK3)
% 4.11/1.00      | v2_struct_0(X1)
% 4.11/1.00      | v2_struct_0(sK3)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ l1_pre_topc(sK3)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_432]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_32,negated_conjecture,
% 4.11/1.00      ( ~ v2_struct_0(sK3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_31,negated_conjecture,
% 4.11/1.00      ( v2_pre_topc(sK3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_437,plain,
% 4.11/1.00      ( ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ v2_pre_topc(X1)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 4.11/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 4.11/1.00      | v2_struct_0(X1)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_433,c_32,c_31,c_30]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_438,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 4.11/1.00      | ~ v2_pre_topc(X1)
% 4.11/1.00      | v2_struct_0(X1)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_437]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_34,negated_conjecture,
% 4.11/1.00      ( v2_pre_topc(sK2) ),
% 4.11/1.00      inference(cnf_transformation,[],[f78]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_501,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 4.11/1.00      | v2_struct_0(X1)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4)
% 4.11/1.00      | sK2 != X1 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_438,c_34]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_502,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | v2_struct_0(sK2)
% 4.11/1.00      | ~ l1_pre_topc(sK2)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0,sK4) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_501]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_35,negated_conjecture,
% 4.11/1.00      ( ~ v2_struct_0(sK2) ),
% 4.11/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_506,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0,sK4) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_502,c_35,c_33]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1785,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ v1_funct_1(X0_55)
% 4.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0_55,sK4) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_506]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2411,plain,
% 4.11/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0_55,sK4)
% 4.11/1.00      | v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 4.11/1.00      | v1_funct_1(X0_55) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3776,plain,
% 4.11/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,sK5,sK4)
% 4.11/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_2406,c_2411]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1799,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 4.11/1.00      | ~ v1_funct_1(X0_55)
% 4.11/1.00      | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2397,plain,
% 4.11/1.00      ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
% 4.11/1.00      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2_55) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1799]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3381,plain,
% 4.11/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55)
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_2406,c_2397]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2771,plain,
% 4.11/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | ~ v1_funct_1(sK5)
% 4.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1799]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3721,plain,
% 4.11/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_3381,c_27,c_25,c_2771]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3777,plain,
% 4.11/1.00      ( k2_tmap_1(sK3,sK2,sK5,sK4) = k7_relat_1(sK5,u1_struct_0(sK4))
% 4.11/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_3776,c_3721]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5066,plain,
% 4.11/1.00      ( k2_tmap_1(sK3,sK2,sK5,sK4) = k7_relat_1(sK5,u1_struct_0(sK4)) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_3777,c_44,c_45]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_14458,plain,
% 4.11/1.00      ( m1_subset_1(sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK3)) = iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_4843,c_5066]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_11,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/1.00      | ~ m1_subset_1(X3,X1)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | v1_xboole_0(X1)
% 4.11/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1798,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 4.11/1.00      | ~ m1_subset_1(X3_55,X1_55)
% 4.11/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 4.11/1.00      | ~ v1_funct_1(X0_55)
% 4.11/1.00      | v1_xboole_0(X1_55)
% 4.11/1.00      | k3_funct_2(X1_55,X2_55,X0_55,X3_55) = k1_funct_1(X0_55,X3_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2398,plain,
% 4.11/1.00      ( k3_funct_2(X0_55,X1_55,X2_55,X3_55) = k1_funct_1(X2_55,X3_55)
% 4.11/1.00      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 4.11/1.00      | m1_subset_1(X3_55,X0_55) != iProver_top
% 4.11/1.00      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2_55) != iProver_top
% 4.11/1.00      | v1_xboole_0(X0_55) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1798]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3462,plain,
% 4.11/1.00      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
% 4.11/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top
% 4.11/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_2406,c_2398]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_573,plain,
% 4.11/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_574,plain,
% 4.11/1.00      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_573]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_575,plain,
% 4.11/1.00      ( l1_struct_0(sK3) != iProver_top
% 4.11/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4594,plain,
% 4.11/1.00      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
% 4.11/1.00      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_3462,c_44,c_45,c_537,c_575]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_14461,plain,
% 4.11/1.00      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_14458,c_4594]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_21,negated_conjecture,
% 4.11/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 4.11/1.00      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 4.11/1.00      | k1_funct_1(sK6,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f91]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1794,negated_conjecture,
% 4.11/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 4.11/1.00      | ~ r2_hidden(X0_55,u1_struct_0(sK4))
% 4.11/1.00      | k1_funct_1(sK6,X0_55) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2402,plain,
% 4.11/1.00      ( k1_funct_1(sK6,X0_55) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_55)
% 4.11/1.00      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 4.11/1.00      | r2_hidden(X0_55,u1_struct_0(sK4)) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1794]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_14462,plain,
% 4.11/1.00      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK6,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
% 4.11/1.00      | r2_hidden(sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4)) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_14458,c_2402]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_14487,plain,
% 4.11/1.00      ( k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK6,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
% 4.11/1.00      | r2_hidden(sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4)) != iProver_top ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_14461,c_14462]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_6,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | v1_relat_1(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f63]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1800,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 4.11/1.00      | v1_relat_1(X0_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2396,plain,
% 4.11/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 4.11/1.00      | v1_relat_1(X0_55) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2920,plain,
% 4.11/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_2406,c_2396]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5,plain,
% 4.11/1.00      ( ~ r2_hidden(X0,X1)
% 4.11/1.00      | ~ v1_relat_1(X2)
% 4.11/1.00      | ~ v1_funct_1(X2)
% 4.11/1.00      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f62]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1801,plain,
% 4.11/1.00      ( ~ r2_hidden(X0_55,X1_55)
% 4.11/1.00      | ~ v1_relat_1(X2_55)
% 4.11/1.00      | ~ v1_funct_1(X2_55)
% 4.11/1.00      | k1_funct_1(k7_relat_1(X2_55,X1_55),X0_55) = k1_funct_1(X2_55,X0_55) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2395,plain,
% 4.11/1.00      ( k1_funct_1(k7_relat_1(X0_55,X1_55),X2_55) = k1_funct_1(X0_55,X2_55)
% 4.11/1.00      | r2_hidden(X2_55,X1_55) != iProver_top
% 4.11/1.00      | v1_relat_1(X0_55) != iProver_top
% 4.11/1.00      | v1_funct_1(X0_55) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4845,plain,
% 4.11/1.00      ( k1_funct_1(k7_relat_1(X0_55,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) = k1_funct_1(X0_55,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6))
% 4.11/1.00      | v1_relat_1(X0_55) != iProver_top
% 4.11/1.00      | v1_funct_1(X0_55) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4838,c_2395]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_8405,plain,
% 4.11/1.00      ( k1_funct_1(k7_relat_1(X0_55,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(X0_55,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
% 4.11/1.00      | v1_relat_1(X0_55) != iProver_top
% 4.11/1.00      | v1_funct_1(X0_55) != iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_4845,c_5066]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_8412,plain,
% 4.11/1.00      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_2920,c_8405]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2709,plain,
% 4.11/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 4.11/1.00      | v1_relat_1(sK5) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1800]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2710,plain,
% 4.11/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 4.11/1.00      | v1_relat_1(sK5) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_2709]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_8410,plain,
% 4.11/1.00      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6))
% 4.11/1.00      | v1_relat_1(sK5) != iProver_top
% 4.11/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_8405]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_8544,plain,
% 4.11/1.00      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_8412,c_44,c_46,c_2710,c_8410]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_7,plain,
% 4.11/1.00      ( r2_funct_2(X0,X1,X2,X3)
% 4.11/1.00      | ~ v1_funct_2(X3,X0,X1)
% 4.11/1.00      | ~ v1_funct_2(X2,X0,X1)
% 4.11/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.11/1.00      | ~ v1_funct_1(X2)
% 4.11/1.00      | ~ v1_funct_1(X3)
% 4.11/1.00      | k1_funct_1(X3,sK1(X0,X2,X3)) != k1_funct_1(X2,sK1(X0,X2,X3)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f66]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_832,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/1.00      | ~ v1_funct_2(X3,X1,X2)
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ v1_funct_1(X3)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k2_tmap_1(sK3,sK2,sK5,sK4) != X3
% 4.11/1.00      | k1_funct_1(X3,sK1(X1,X3,X0)) != k1_funct_1(X0,sK1(X1,X3,X0))
% 4.11/1.00      | u1_struct_0(sK2) != X2
% 4.11/1.00      | u1_struct_0(sK4) != X1
% 4.11/1.00      | sK6 != X0 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_833,plain,
% 4.11/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
% 4.11/1.00      | ~ v1_funct_1(sK6)
% 4.11/1.00      | k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_832]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_835,plain,
% 4.11/1.00      ( ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
% 4.11/1.00      | ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_833,c_24,c_23,c_22]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_836,plain,
% 4.11/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
% 4.11/1.00      | k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_835]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1775,plain,
% 4.11/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 4.11/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 4.11/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
% 4.11/1.00      | k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
% 4.11/1.00      inference(subtyping,[status(esa)],[c_836]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2421,plain,
% 4.11/1.00      ( k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6))
% 4.11/1.00      | v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 4.11/1.00      | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4)) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_74,plain,
% 4.11/1.00      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4304,plain,
% 4.11/1.00      ( k1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4),sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2421,c_33,c_27,c_26,c_25,c_74,c_536,c_550,c_1775,
% 4.11/1.00                 c_2858,c_3070,c_3310]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5070,plain,
% 4.11/1.00      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK4)),sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_5066,c_4304]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_8547,plain,
% 4.11/1.00      ( k1_funct_1(sK5,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) != k1_funct_1(sK6,sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6)) ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_8544,c_5070]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5069,plain,
% 4.11/1.00      ( r2_hidden(sK1(u1_struct_0(sK4),k7_relat_1(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4)) = iProver_top ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_5066,c_4838]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(contradiction,plain,
% 4.11/1.00      ( $false ),
% 4.11/1.00      inference(minisat,[status(thm)],[c_14487,c_8547,c_5069]) ).
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  ------                               Statistics
% 4.11/1.00  
% 4.11/1.00  ------ General
% 4.11/1.00  
% 4.11/1.00  abstr_ref_over_cycles:                  0
% 4.11/1.00  abstr_ref_under_cycles:                 0
% 4.11/1.00  gc_basic_clause_elim:                   0
% 4.11/1.00  forced_gc_time:                         0
% 4.11/1.00  parsing_time:                           0.011
% 4.11/1.00  unif_index_cands_time:                  0.
% 4.11/1.00  unif_index_add_time:                    0.
% 4.11/1.00  orderings_time:                         0.
% 4.11/1.00  out_proof_time:                         0.015
% 4.11/1.00  total_time:                             0.472
% 4.11/1.00  num_of_symbols:                         61
% 4.11/1.00  num_of_terms:                           11656
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing
% 4.11/1.00  
% 4.11/1.00  num_of_splits:                          0
% 4.11/1.00  num_of_split_atoms:                     0
% 4.11/1.00  num_of_reused_defs:                     0
% 4.11/1.00  num_eq_ax_congr_red:                    27
% 4.11/1.00  num_of_sem_filtered_clauses:            1
% 4.11/1.00  num_of_subtypes:                        3
% 4.11/1.00  monotx_restored_types:                  0
% 4.11/1.00  sat_num_of_epr_types:                   0
% 4.11/1.00  sat_num_of_non_cyclic_types:            0
% 4.11/1.00  sat_guarded_non_collapsed_types:        0
% 4.11/1.00  num_pure_diseq_elim:                    0
% 4.11/1.00  simp_replaced_by:                       0
% 4.11/1.00  res_preprocessed:                       165
% 4.11/1.00  prep_upred:                             0
% 4.11/1.00  prep_unflattend:                        78
% 4.11/1.00  smt_new_axioms:                         0
% 4.11/1.00  pred_elim_cands:                        7
% 4.11/1.00  pred_elim:                              5
% 4.11/1.00  pred_elim_cl:                           4
% 4.11/1.00  pred_elim_cycles:                       11
% 4.11/1.00  merged_defs:                            0
% 4.11/1.00  merged_defs_ncl:                        0
% 4.11/1.00  bin_hyper_res:                          0
% 4.11/1.00  prep_cycles:                            4
% 4.11/1.00  pred_elim_time:                         0.022
% 4.11/1.00  splitting_time:                         0.
% 4.11/1.00  sem_filter_time:                        0.
% 4.11/1.00  monotx_time:                            0.
% 4.11/1.00  subtype_inf_time:                       0.
% 4.11/1.00  
% 4.11/1.00  ------ Problem properties
% 4.11/1.00  
% 4.11/1.00  clauses:                                32
% 4.11/1.00  conjectures:                            7
% 4.11/1.00  epr:                                    7
% 4.11/1.00  horn:                                   28
% 4.11/1.00  ground:                                 15
% 4.11/1.00  unary:                                  13
% 4.11/1.00  binary:                                 3
% 4.11/1.00  lits:                                   99
% 4.11/1.00  lits_eq:                                10
% 4.11/1.00  fd_pure:                                0
% 4.11/1.00  fd_pseudo:                              0
% 4.11/1.00  fd_cond:                                0
% 4.11/1.00  fd_pseudo_cond:                         0
% 4.11/1.00  ac_symbols:                             0
% 4.11/1.00  
% 4.11/1.00  ------ Propositional Solver
% 4.11/1.00  
% 4.11/1.00  prop_solver_calls:                      31
% 4.11/1.00  prop_fast_solver_calls:                 2011
% 4.11/1.00  smt_solver_calls:                       0
% 4.11/1.00  smt_fast_solver_calls:                  0
% 4.11/1.00  prop_num_of_clauses:                    5076
% 4.11/1.00  prop_preprocess_simplified:             10911
% 4.11/1.00  prop_fo_subsumed:                       146
% 4.11/1.00  prop_solver_time:                       0.
% 4.11/1.00  smt_solver_time:                        0.
% 4.11/1.00  smt_fast_solver_time:                   0.
% 4.11/1.00  prop_fast_solver_time:                  0.
% 4.11/1.00  prop_unsat_core_time:                   0.
% 4.11/1.00  
% 4.11/1.00  ------ QBF
% 4.11/1.00  
% 4.11/1.00  qbf_q_res:                              0
% 4.11/1.00  qbf_num_tautologies:                    0
% 4.11/1.00  qbf_prep_cycles:                        0
% 4.11/1.00  
% 4.11/1.00  ------ BMC1
% 4.11/1.00  
% 4.11/1.00  bmc1_current_bound:                     -1
% 4.11/1.00  bmc1_last_solved_bound:                 -1
% 4.11/1.00  bmc1_unsat_core_size:                   -1
% 4.11/1.00  bmc1_unsat_core_parents_size:           -1
% 4.11/1.00  bmc1_merge_next_fun:                    0
% 4.11/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.11/1.00  
% 4.11/1.00  ------ Instantiation
% 4.11/1.00  
% 4.11/1.00  inst_num_of_clauses:                    1462
% 4.11/1.00  inst_num_in_passive:                    609
% 4.11/1.00  inst_num_in_active:                     816
% 4.11/1.00  inst_num_in_unprocessed:                45
% 4.11/1.00  inst_num_of_loops:                      880
% 4.11/1.00  inst_num_of_learning_restarts:          0
% 4.11/1.00  inst_num_moves_active_passive:          59
% 4.11/1.00  inst_lit_activity:                      0
% 4.11/1.00  inst_lit_activity_moves:                0
% 4.11/1.00  inst_num_tautologies:                   0
% 4.11/1.00  inst_num_prop_implied:                  0
% 4.11/1.00  inst_num_existing_simplified:           0
% 4.11/1.00  inst_num_eq_res_simplified:             0
% 4.11/1.00  inst_num_child_elim:                    0
% 4.11/1.00  inst_num_of_dismatching_blockings:      824
% 4.11/1.00  inst_num_of_non_proper_insts:           1632
% 4.11/1.00  inst_num_of_duplicates:                 0
% 4.11/1.00  inst_inst_num_from_inst_to_res:         0
% 4.11/1.00  inst_dismatching_checking_time:         0.
% 4.11/1.00  
% 4.11/1.00  ------ Resolution
% 4.11/1.00  
% 4.11/1.00  res_num_of_clauses:                     0
% 4.11/1.00  res_num_in_passive:                     0
% 4.11/1.00  res_num_in_active:                      0
% 4.11/1.00  res_num_of_loops:                       169
% 4.11/1.00  res_forward_subset_subsumed:            139
% 4.11/1.00  res_backward_subset_subsumed:           20
% 4.11/1.00  res_forward_subsumed:                   2
% 4.11/1.00  res_backward_subsumed:                  0
% 4.11/1.00  res_forward_subsumption_resolution:     0
% 4.11/1.00  res_backward_subsumption_resolution:    0
% 4.11/1.00  res_clause_to_clause_subsumption:       528
% 4.11/1.00  res_orphan_elimination:                 0
% 4.11/1.00  res_tautology_del:                      338
% 4.11/1.00  res_num_eq_res_simplified:              0
% 4.11/1.00  res_num_sel_changes:                    0
% 4.11/1.00  res_moves_from_active_to_pass:          0
% 4.11/1.00  
% 4.11/1.00  ------ Superposition
% 4.11/1.00  
% 4.11/1.00  sup_time_total:                         0.
% 4.11/1.00  sup_time_generating:                    0.
% 4.11/1.00  sup_time_sim_full:                      0.
% 4.11/1.00  sup_time_sim_immed:                     0.
% 4.11/1.00  
% 4.11/1.00  sup_num_of_clauses:                     254
% 4.11/1.00  sup_num_in_active:                      171
% 4.11/1.00  sup_num_in_passive:                     83
% 4.11/1.00  sup_num_of_loops:                       175
% 4.11/1.00  sup_fw_superposition:                   136
% 4.11/1.00  sup_bw_superposition:                   107
% 4.11/1.00  sup_immediate_simplified:               15
% 4.11/1.00  sup_given_eliminated:                   0
% 4.11/1.00  comparisons_done:                       0
% 4.11/1.00  comparisons_avoided:                    0
% 4.11/1.00  
% 4.11/1.00  ------ Simplifications
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  sim_fw_subset_subsumed:                 4
% 4.11/1.00  sim_bw_subset_subsumed:                 1
% 4.11/1.00  sim_fw_subsumed:                        0
% 4.11/1.00  sim_bw_subsumed:                        0
% 4.11/1.00  sim_fw_subsumption_res:                 3
% 4.11/1.00  sim_bw_subsumption_res:                 0
% 4.11/1.00  sim_tautology_del:                      6
% 4.11/1.00  sim_eq_tautology_del:                   4
% 4.11/1.00  sim_eq_res_simp:                        0
% 4.11/1.00  sim_fw_demodulated:                     1
% 4.11/1.00  sim_bw_demodulated:                     6
% 4.11/1.00  sim_light_normalised:                   12
% 4.11/1.00  sim_joinable_taut:                      0
% 4.11/1.00  sim_joinable_simp:                      0
% 4.11/1.00  sim_ac_normalised:                      0
% 4.11/1.00  sim_smt_subsumption:                    0
% 4.11/1.00  
%------------------------------------------------------------------------------
