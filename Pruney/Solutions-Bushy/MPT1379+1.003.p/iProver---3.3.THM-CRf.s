%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1379+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:35 EST 2020

% Result     : Theorem 39.05s
% Output     : CNFRefutation 39.05s
% Verified   : 
% Statistics : Number of formulae       :  177 (1495 expanded)
%              Number of clauses        :  113 ( 331 expanded)
%              Number of leaves         :   17 ( 459 expanded)
%              Depth                    :   24
%              Number of atoms          :  714 (13750 expanded)
%              Number of equality atoms :  161 ( 357 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
            | ~ m1_connsp_2(X3,X0,X1)
            | ~ m1_connsp_2(X2,X0,X1) )
          & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
            | ( m1_connsp_2(X3,X0,X1)
              & m1_connsp_2(X2,X0,X1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,sK4),X0,X1)
          | ~ m1_connsp_2(sK4,X0,X1)
          | ~ m1_connsp_2(X2,X0,X1) )
        & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,sK4),X0,X1)
          | ( m1_connsp_2(sK4,X0,X1)
            & m1_connsp_2(X2,X0,X1) ) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                | ~ m1_connsp_2(X3,X0,X1)
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                | ( m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),sK3,X3),X0,X1)
              | ~ m1_connsp_2(X3,X0,X1)
              | ~ m1_connsp_2(sK3,X0,X1) )
            & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),sK3,X3),X0,X1)
              | ( m1_connsp_2(X3,X0,X1)
                & m1_connsp_2(sK3,X0,X1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,sK2)
                  | ~ m1_connsp_2(X3,X0,sK2)
                  | ~ m1_connsp_2(X2,X0,sK2) )
                & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,sK2)
                  | ( m1_connsp_2(X3,X0,sK2)
                    & m1_connsp_2(X2,X0,sK2) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1)
                    | ~ m1_connsp_2(X3,sK1,X1)
                    | ~ m1_connsp_2(X2,sK1,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1)
                    | ( m1_connsp_2(X3,sK1,X1)
                      & m1_connsp_2(X2,sK1,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
      | ~ m1_connsp_2(sK4,sK1,sK2)
      | ~ m1_connsp_2(sK3,sK1,sK2) )
    & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
      | ( m1_connsp_2(sK4,sK1,sK2)
        & m1_connsp_2(sK3,sK1,sK2) ) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f34,f38,f37,f36,f35])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | ~ m1_connsp_2(sK4,sK1,sK2)
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f62,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_930,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_923,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_935,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1823,plain,
    ( k9_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,X1)) = k3_xboole_0(X0,k1_tops_1(sK1,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_935])).

cnf(c_6703,plain,
    ( k9_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,sK4)) = k3_xboole_0(X0,k1_tops_1(sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_930,c_1823])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_929,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X0)) = k1_tops_1(X1,k9_subset_1(u1_struct_0(X1),X2,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X0)) = k1_tops_1(X1,k9_subset_1(u1_struct_0(X1),X2,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X1,X0)) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_21])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X1,X0)) ),
    inference(renaming,[status(thm)],[c_352])).

cnf(c_924,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_1405,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_924])).

cnf(c_2773,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_930,c_1405])).

cnf(c_1821,plain,
    ( k9_subset_1(u1_struct_0(sK1),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_930,c_935])).

cnf(c_2784,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k1_tops_1(sK1,k3_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_2773,c_1821])).

cnf(c_6862,plain,
    ( k3_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k1_tops_1(sK1,k3_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_6703,c_2784])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_939,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7549,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,k3_xboole_0(sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6862,c_939])).

cnf(c_1,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_310,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_311,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_315,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_22,c_21])).

cnf(c_925,plain,
    ( m1_connsp_2(X0,sK1,X1) = iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1928,plain,
    ( ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_14,c_373])).

cnf(c_2032,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1928,c_315])).

cnf(c_2034,plain,
    ( m1_connsp_2(X0,sK1,X1) = iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2032])).

cnf(c_2797,plain,
    ( r2_hidden(X1,k1_tops_1(sK1,X0)) != iProver_top
    | m1_connsp_2(X0,sK1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_925,c_2034])).

cnf(c_2798,plain,
    ( m1_connsp_2(X0,sK1,X1) = iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2797])).

cnf(c_94650,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top
    | m1_subset_1(k3_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7549,c_2798])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_936,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1899,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_936])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5249,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1899,c_29])).

cnf(c_109667,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_94650,c_5249])).

cnf(c_15,negated_conjecture,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | ~ m1_connsp_2(sK4,sK1,sK2)
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_933,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) != iProver_top
    | m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1881,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,sK2) != iProver_top
    | m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1821,c_933])).

cnf(c_109672,plain,
    ( m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_109667,c_1881])).

cnf(c_539,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3285,plain,
    ( ~ r2_hidden(X0,k9_subset_1(X1,X2,X3))
    | r2_hidden(X4,k9_subset_1(X1,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | X4 != X0 ),
    inference(resolution,[status(thm)],[c_539,c_0])).

cnf(c_3297,plain,
    ( r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X2)))
    | ~ r2_hidden(X3,k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != X3 ),
    inference(resolution,[status(thm)],[c_539,c_353])).

cnf(c_2,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_144,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_11])).

cnf(c_145,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_268,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_23])).

cnf(c_269,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_273,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_269,c_22,c_21])).

cnf(c_3652,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK1),X0,X1),sK1,X2)
    | r2_hidden(X3,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_3297,c_273])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3671,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_3652,c_17])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3830,plain,
    ( r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | m1_connsp_2(sK3,sK1,sK2)
    | X0 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3671,c_20,c_19,c_18])).

cnf(c_3831,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | X0 != sK2 ),
    inference(renaming,[status(thm)],[c_3830])).

cnf(c_10795,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != X1
    | X1 != sK2 ),
    inference(resolution,[status(thm)],[c_3285,c_3831])).

cnf(c_1103,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_11031,plain,
    ( r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)))
    | m1_connsp_2(sK3,sK1,sK2)
    | X0 != X1
    | X1 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10795,c_18,c_1103])).

cnf(c_11032,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)))
    | X0 != X1
    | X1 != sK2 ),
    inference(renaming,[status(thm)],[c_11031])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11296,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)))
    | r2_hidden(sK0(X1,X2,sK2),X2)
    | r2_hidden(sK0(X1,X2,sK2),sK2)
    | X0 != k3_xboole_0(X1,X2) ),
    inference(resolution,[status(thm)],[c_11032,c_4])).

cnf(c_2888,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_931,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1880,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK3,sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1821,c_931])).

cnf(c_927,plain,
    ( m1_connsp_2(X0,sK1,X1) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_937,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7551,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,k3_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6862,c_937])).

cnf(c_11489,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_7551])).

cnf(c_12091,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1880,c_11489])).

cnf(c_12105,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12091])).

cnf(c_13014,plain,
    ( m1_connsp_2(sK3,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11296,c_20,c_19,c_2888,c_12105])).

cnf(c_13016,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13014])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3670,plain,
    ( m1_connsp_2(sK4,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_3652,c_16])).

cnf(c_3679,plain,
    ( r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | m1_connsp_2(sK4,sK1,sK2)
    | X0 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3670,c_20,c_19,c_18])).

cnf(c_3680,plain,
    ( m1_connsp_2(sK4,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | X0 != sK2 ),
    inference(renaming,[status(thm)],[c_3679])).

cnf(c_10794,plain,
    ( m1_connsp_2(sK4,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != X1
    | X1 != sK2 ),
    inference(resolution,[status(thm)],[c_3285,c_3680])).

cnf(c_10978,plain,
    ( r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)))
    | m1_connsp_2(sK4,sK1,sK2)
    | X0 != X1
    | X1 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10794,c_18,c_1103])).

cnf(c_10979,plain,
    ( m1_connsp_2(sK4,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)))
    | X0 != X1
    | X1 != sK2 ),
    inference(renaming,[status(thm)],[c_10978])).

cnf(c_532,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_11010,plain,
    ( m1_connsp_2(sK4,sK1,sK2)
    | r2_hidden(X0,k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)))
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_10979,c_532])).

cnf(c_2870,plain,
    ( m1_connsp_2(sK4,sK1,sK2)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_932,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1879,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK4,sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1821,c_932])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_938,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7550,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,k3_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6862,c_938])).

cnf(c_10428,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_7550])).

cnf(c_11220,plain,
    ( m1_connsp_2(sK4,sK1,sK2) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_10428])).

cnf(c_11234,plain,
    ( m1_connsp_2(sK4,sK1,sK2)
    | r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11220])).

cnf(c_11403,plain,
    ( m1_connsp_2(sK4,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11010,c_20,c_18,c_2870,c_11234])).

cnf(c_11405,plain,
    ( m1_connsp_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11403])).

cnf(c_1114,plain,
    ( ~ m1_connsp_2(X0,sK1,sK2)
    | r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_1394,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_1395,plain,
    ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_1391,plain,
    ( ~ m1_connsp_2(sK4,sK1,sK2)
    | r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_1392,plain,
    ( m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109672,c_13016,c_11405,c_1395,c_1392,c_27])).


%------------------------------------------------------------------------------
