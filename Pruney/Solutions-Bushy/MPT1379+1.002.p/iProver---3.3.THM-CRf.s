%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1379+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:35 EST 2020

% Result     : Theorem 55.51s
% Output     : CNFRefutation 55.51s
% Verified   : 
% Statistics : Number of formulae       :  176 (3385 expanded)
%              Number of clauses        :  118 ( 803 expanded)
%              Number of leaves         :   17 (1022 expanded)
%              Depth                    :   32
%              Number of atoms          :  675 (30161 expanded)
%              Number of equality atoms :  210 (1047 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f34,f33,f32,f31])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f57,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | ~ m1_connsp_2(sK4,sK1,sK2)
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_842,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_846,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1631,plain,
    ( k9_subset_1(u1_struct_0(sK1),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_842,c_846])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_843,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1687,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK3,sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1631,c_843])).

cnf(c_2,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_133,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_11])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_247,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_133,c_22])).

cnf(c_248,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_252,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_248,c_21,c_20])).

cnf(c_839,plain,
    ( m1_connsp_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_835,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_1633,plain,
    ( k9_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,X1)) = k3_xboole_0(X0,k1_tops_1(sK1,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_846])).

cnf(c_5223,plain,
    ( k9_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,sK4)) = k3_xboole_0(X0,k1_tops_1(sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_842,c_1633])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_841,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X0)) = k1_tops_1(X1,k9_subset_1(u1_struct_0(X1),X2,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X0)) = k1_tops_1(X1,k9_subset_1(u1_struct_0(X1),X2,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X1,X0)) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_20])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X1,X0)) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_836,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1254,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_836])).

cnf(c_2533,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_842,c_1254])).

cnf(c_2544,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k1_tops_1(sK1,k3_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_2533,c_1631])).

cnf(c_5923,plain,
    ( k3_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k1_tops_1(sK1,k3_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_5223,c_2544])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_848,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6159,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,k3_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5923,c_848])).

cnf(c_160041,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_6159])).

cnf(c_161170,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_160041])).

cnf(c_15,negated_conjecture,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_844,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1686,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK4,sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1631,c_844])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_849,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6158,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,k3_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5923,c_849])).

cnf(c_156458,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_6158])).

cnf(c_157261,plain,
    ( m1_connsp_2(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1686,c_156458])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_850,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6157,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,k3_xboole_0(sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5923,c_850])).

cnf(c_1,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_289,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_290,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_294,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_21,c_20])).

cnf(c_837,plain,
    ( m1_connsp_2(X0,sK1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_153601,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6157,c_837])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1024,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2709,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_2710,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2709])).

cnf(c_498,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3768,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5224,plain,
    ( k9_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,sK3)) = k3_xboole_0(X0,k1_tops_1(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_841,c_1633])).

cnf(c_1253,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_842,c_836])).

cnf(c_2215,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,k9_subset_1(u1_struct_0(sK1),sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_841,c_1253])).

cnf(c_1632,plain,
    ( k9_subset_1(u1_struct_0(sK1),X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_841,c_846])).

cnf(c_2222,plain,
    ( k9_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,k3_xboole_0(sK4,sK3)) ),
    inference(demodulation,[status(thm)],[c_2215,c_1632])).

cnf(c_6115,plain,
    ( k3_xboole_0(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,k3_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_5224,c_2222])).

cnf(c_6207,plain,
    ( k3_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k1_tops_1(sK1,k3_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_0,c_6115])).

cnf(c_6229,plain,
    ( k1_tops_1(sK1,k3_xboole_0(sK3,sK4)) = k1_tops_1(sK1,k3_xboole_0(sK4,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_6207,c_5923])).

cnf(c_7569,plain,
    ( m1_connsp_2(k3_xboole_0(sK4,sK3),sK1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_xboole_0(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,k3_xboole_0(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6229,c_837])).

cnf(c_7570,plain,
    ( m1_connsp_2(k3_xboole_0(sK4,sK3),sK1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,k3_xboole_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6229,c_839])).

cnf(c_7950,plain,
    ( m1_connsp_2(k3_xboole_0(sK4,sK3),sK1,X0) != iProver_top
    | m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7570,c_837])).

cnf(c_847,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2563,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_847])).

cnf(c_3358,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2563,c_28])).

cnf(c_17668,plain,
    ( m1_connsp_2(k3_xboole_0(sK4,sK3),sK1,X0) != iProver_top
    | m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7950,c_3358])).

cnf(c_98727,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_112324,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_98727])).

cnf(c_499,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_103054,plain,
    ( X0 != X1
    | X0 = k9_subset_1(u1_struct_0(sK1),sK3,sK4)
    | k9_subset_1(u1_struct_0(sK1),sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_112323,plain,
    ( X0 = k9_subset_1(u1_struct_0(sK1),sK3,sK4)
    | X0 != k3_xboole_0(sK3,sK4)
    | k9_subset_1(u1_struct_0(sK1),sK3,sK4) != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_103054])).

cnf(c_118545,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK3,sK4) != k3_xboole_0(sK3,sK4)
    | k3_xboole_0(sK4,sK3) = k9_subset_1(u1_struct_0(sK1),sK3,sK4)
    | k3_xboole_0(sK4,sK3) != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_112323])).

cnf(c_118546,plain,
    ( k3_xboole_0(sK4,sK3) = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_99400,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X2,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != k9_subset_1(u1_struct_0(sK1),X2,sK4)
    | X1 != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_114471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X2,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != k9_subset_1(u1_struct_0(sK1),X2,sK4)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_99400])).

cnf(c_146908,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_xboole_0(sK4,sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | k3_xboole_0(sK4,sK3) != k9_subset_1(u1_struct_0(sK1),sK3,sK4)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_114471])).

cnf(c_146909,plain,
    ( k3_xboole_0(sK4,sK3) != k9_subset_1(u1_struct_0(sK1),sK3,sK4)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_xboole_0(sK4,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146908])).

cnf(c_146911,plain,
    ( k3_xboole_0(sK4,sK3) != k9_subset_1(u1_struct_0(sK1),sK3,sK4)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_xboole_0(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_146909])).

cnf(c_154332,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_153601,c_17,c_28,c_2710,c_3768,c_6157,c_7569,c_17668,c_112324,c_118545,c_118546,c_146911])).

cnf(c_154333,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_154332])).

cnf(c_14,negated_conjecture,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    | ~ m1_connsp_2(sK4,sK1,sK2)
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_845,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) != iProver_top
    | m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1688,plain,
    ( m1_connsp_2(k3_xboole_0(sK3,sK4),sK1,sK2) != iProver_top
    | m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1631,c_845])).

cnf(c_154343,plain,
    ( m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_154333,c_1688])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1005,plain,
    ( m1_connsp_2(X0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_1202,plain,
    ( m1_connsp_2(sK4,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_1203,plain,
    ( m1_connsp_2(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1202])).

cnf(c_1205,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_1206,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(c_154361,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK4)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_154343,c_26,c_27,c_28,c_1203,c_1206])).

cnf(c_154367,plain,
    ( m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_154361])).

cnf(c_154380,plain,
    ( m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_154367,c_26])).

cnf(c_154386,plain,
    ( m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_154380])).

cnf(c_29,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_30,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) = iProver_top
    | m1_connsp_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_31,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) != iProver_top
    | m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_154389,plain,
    ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | m1_connsp_2(sK4,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_154386,c_26,c_29,c_30,c_31])).

cnf(c_154390,plain,
    ( m1_connsp_2(sK4,sK1,sK2) != iProver_top
    | m1_connsp_2(sK3,sK1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_154389])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_161170,c_157261,c_154390,c_154367,c_1203,c_28,c_26])).


%------------------------------------------------------------------------------
