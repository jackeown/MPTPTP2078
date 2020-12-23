%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:49 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  196 (2497 expanded)
%              Number of clauses        :  121 ( 540 expanded)
%              Number of leaves         :   19 ( 750 expanded)
%              Depth                    :   27
%              Number of atoms          :  787 (24542 expanded)
%              Number of equality atoms :  227 (4625 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X2)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
     => ( ( ! [X4] :
              ( sK3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) )
          | ! [X5] :
              ( sK3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
        & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,sK2))) )
        & ~ r1_tsep_1(X1,sK2)
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,sK1,X2))) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( X3 != X4
                          | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                      | ! [X5] :
                          ( X3 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                    & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | ! [X5] :
          ( sK3 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
    & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43,f42,f41,f40])).

fof(f72,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X4,X5] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f76,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f75])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6748,plain,
    ( ~ v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | v1_xboole_0(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_21])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2428,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_19,c_7])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1199,plain,
    ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_6,c_21])).

cnf(c_2598,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | r2_hidden(sK3,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_2428,c_1199])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5718,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | r2_hidden(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_2598,c_16])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6543,plain,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5718,c_28,c_27,c_26,c_25,c_24,c_23])).

cnf(c_6756,plain,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v1_xboole_0(sK3) ),
    inference(resolution,[status(thm)],[c_6748,c_6543])).

cnf(c_6876,plain,
    ( ~ m1_pre_topc(sK0,X0)
    | r2_hidden(sK3,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK3) ),
    inference(resolution,[status(thm)],[c_6756,c_2428])).

cnf(c_784,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_799,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2108,plain,
    ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_799])).

cnf(c_782,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_780,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
    | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ l1_pre_topc(X2)
    | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_790,plain,
    ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | r1_tsep_1(X1,X2) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,X1,X2)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,X1,X2)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_787,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X1,X0,X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_788,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | v1_pre_topc(k2_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_789,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_982,plain,
    ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | r1_tsep_1(X1,X2) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_790,c_787,c_788,c_789])).

cnf(c_4812,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
    | r1_tsep_1(sK1,X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_982])).

cnf(c_29,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6681,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tsep_1(sK1,X0) = iProver_top
    | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4812,c_29,c_30,c_31])).

cnf(c_6682,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
    | r1_tsep_1(sK1,X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6681])).

cnf(c_6692,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_6682])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1129,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v1_pre_topc(k2_tsep_1(sK0,X0,sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1267,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_1161,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1296,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_1352,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1906,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6824,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6692,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_1267,c_1296,c_1352,c_1906])).

cnf(c_786,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_797,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1974,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,u1_struct_0(X2)) = k3_xboole_0(X1,u1_struct_0(X2))
    | m1_pre_topc(X2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_797])).

cnf(c_5190,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_1974])).

cnf(c_1090,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1220,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5224,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5190,c_27,c_23,c_1090,c_1220])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k9_subset_1(u1_struct_0(X1),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_792,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X1),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5224,c_792])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_793,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2920,plain,
    ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1))) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_793])).

cnf(c_3743,plain,
    ( u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) = u1_struct_0(sK2)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_2920])).

cnf(c_1230,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3930,plain,
    ( u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3743,c_27,c_23,c_1090,c_1230])).

cnf(c_5229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5228,c_3930])).

cnf(c_34,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1091,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1090])).

cnf(c_7961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5229,c_30,c_34,c_1091])).

cnf(c_7969,plain,
    ( m1_subset_1(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6824,c_7961])).

cnf(c_32,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1093,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1094,plain,
    ( m1_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_8034,plain,
    ( m1_subset_1(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7969,c_30,c_32,c_1094])).

cnf(c_798,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8041,plain,
    ( r2_hidden(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8034,c_798])).

cnf(c_8436,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2108,c_8041])).

cnf(c_800,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2130,plain,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_800])).

cnf(c_8893,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8436,c_2130])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_802,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9767,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8893,c_802])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_208,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_2])).

cnf(c_209,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_1759,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_20,c_209])).

cnf(c_1760,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_1,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_803,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6827,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6824,c_803])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_804,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2564,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X0) != iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2108,c_804])).

cnf(c_6939,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6827,c_2564])).

cnf(c_776,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_9768,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8893,c_776])).

cnf(c_10318,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9767,c_1760,c_2130,c_6939,c_9768])).

cnf(c_10320,plain,
    ( v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10318])).

cnf(c_28543,plain,
    ( v1_xboole_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6876,c_10320])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6569,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_20])).

cnf(c_28594,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_28543,c_6569])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7003,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_794,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22433,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6939,c_794])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1907,plain,
    ( m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1906])).

cnf(c_22443,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
    | l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22433,c_29,c_30,c_31,c_32,c_33,c_34,c_1907])).

cnf(c_22445,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22443])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24988,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_24990,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_24988])).

cnf(c_28598,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28594,c_28,c_27,c_26,c_25,c_24,c_23,c_1296,c_1759,c_7003,c_22445,c_24990])).

cnf(c_28610,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_28598,c_209])).

cnf(c_8892,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8436,c_794])).

cnf(c_8904,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8892])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28610,c_24990,c_8904,c_7003,c_1906,c_1296,c_23,c_24,c_25,c_26,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.00/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.00/1.50  
% 8.00/1.50  ------  iProver source info
% 8.00/1.50  
% 8.00/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.00/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.00/1.50  git: non_committed_changes: false
% 8.00/1.50  git: last_make_outside_of_git: false
% 8.00/1.50  
% 8.00/1.50  ------ 
% 8.00/1.50  ------ Parsing...
% 8.00/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.00/1.50  ------ Proving...
% 8.00/1.50  ------ Problem Properties 
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  clauses                                 29
% 8.00/1.50  conjectures                             9
% 8.00/1.50  EPR                                     15
% 8.00/1.50  Horn                                    23
% 8.00/1.50  unary                                   9
% 8.00/1.50  binary                                  5
% 8.00/1.50  lits                                    94
% 8.00/1.50  lits eq                                 5
% 8.00/1.50  fd_pure                                 0
% 8.00/1.50  fd_pseudo                               0
% 8.00/1.50  fd_cond                                 0
% 8.00/1.50  fd_pseudo_cond                          1
% 8.00/1.50  AC symbols                              0
% 8.00/1.50  
% 8.00/1.50  ------ Input Options Time Limit: Unbounded
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  ------ 
% 8.00/1.50  Current options:
% 8.00/1.50  ------ 
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  ------ Proving...
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  % SZS status Theorem for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  fof(f4,axiom,(
% 8.00/1.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f22,plain,(
% 8.00/1.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f4])).
% 8.00/1.50  
% 8.00/1.50  fof(f38,plain,(
% 8.00/1.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 8.00/1.50    inference(nnf_transformation,[],[f22])).
% 8.00/1.50  
% 8.00/1.50  fof(f50,plain,(
% 8.00/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f38])).
% 8.00/1.50  
% 8.00/1.50  fof(f15,conjecture,(
% 8.00/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f16,negated_conjecture,(
% 8.00/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 8.00/1.50    inference(negated_conjecture,[],[f15])).
% 8.00/1.50  
% 8.00/1.50  fof(f17,plain,(
% 8.00/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 8.00/1.50    inference(rectify,[],[f16])).
% 8.00/1.50  
% 8.00/1.50  fof(f19,plain,(
% 8.00/1.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 8.00/1.50    inference(pure_predicate_removal,[],[f17])).
% 8.00/1.50  
% 8.00/1.50  fof(f36,plain,(
% 8.00/1.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f19])).
% 8.00/1.50  
% 8.00/1.50  fof(f37,plain,(
% 8.00/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.00/1.50    inference(flattening,[],[f36])).
% 8.00/1.50  
% 8.00/1.50  fof(f43,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) => ((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(X0,X1,X2))))) )),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f42,plain,(
% 8.00/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,sK2)))) & ~r1_tsep_1(X1,sK2) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f41,plain,(
% 8.00/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f40,plain,(
% 8.00/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f44,plain,(
% 8.00/1.50    ((((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 8.00/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43,f42,f41,f40])).
% 8.00/1.50  
% 8.00/1.50  fof(f72,plain,(
% 8.00/1.50    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f14,axiom,(
% 8.00/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f35,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f14])).
% 8.00/1.50  
% 8.00/1.50  fof(f64,plain,(
% 8.00/1.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f35])).
% 8.00/1.50  
% 8.00/1.50  fof(f5,axiom,(
% 8.00/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f23,plain,(
% 8.00/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f5])).
% 8.00/1.50  
% 8.00/1.50  fof(f52,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f23])).
% 8.00/1.50  
% 8.00/1.50  fof(f48,plain,(
% 8.00/1.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f38])).
% 8.00/1.50  
% 8.00/1.50  fof(f13,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f33,plain,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f13])).
% 8.00/1.50  
% 8.00/1.50  fof(f34,plain,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(flattening,[],[f33])).
% 8.00/1.50  
% 8.00/1.50  fof(f63,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f34])).
% 8.00/1.50  
% 8.00/1.50  fof(f65,plain,(
% 8.00/1.50    ~v2_struct_0(sK0)),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f66,plain,(
% 8.00/1.50    l1_pre_topc(sK0)),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f67,plain,(
% 8.00/1.50    ~v2_struct_0(sK1)),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f68,plain,(
% 8.00/1.50    m1_pre_topc(sK1,sK0)),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f69,plain,(
% 8.00/1.50    ~v2_struct_0(sK2)),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f70,plain,(
% 8.00/1.50    m1_pre_topc(sK2,sK0)),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f12,axiom,(
% 8.00/1.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)))))))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f31,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f12])).
% 8.00/1.50  
% 8.00/1.50  fof(f32,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(flattening,[],[f31])).
% 8.00/1.50  
% 8.00/1.50  fof(f39,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(nnf_transformation,[],[f32])).
% 8.00/1.50  
% 8.00/1.50  fof(f59,plain,(
% 8.00/1.50    ( ! [X2,X0,X3,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f39])).
% 8.00/1.50  
% 8.00/1.50  fof(f74,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(equality_resolution,[],[f59])).
% 8.00/1.50  
% 8.00/1.50  fof(f61,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f34])).
% 8.00/1.50  
% 8.00/1.50  fof(f62,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f34])).
% 8.00/1.50  
% 8.00/1.50  fof(f71,plain,(
% 8.00/1.50    ~r1_tsep_1(sK1,sK2)),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f6,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f24,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f6])).
% 8.00/1.50  
% 8.00/1.50  fof(f53,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f24])).
% 8.00/1.50  
% 8.00/1.50  fof(f11,axiom,(
% 8.00/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f30,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f11])).
% 8.00/1.50  
% 8.00/1.50  fof(f58,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f30])).
% 8.00/1.50  
% 8.00/1.50  fof(f10,axiom,(
% 8.00/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f29,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f10])).
% 8.00/1.50  
% 8.00/1.50  fof(f57,plain,(
% 8.00/1.50    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f29])).
% 8.00/1.50  
% 8.00/1.50  fof(f3,axiom,(
% 8.00/1.50    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f21,plain,(
% 8.00/1.50    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 8.00/1.50    inference(ennf_transformation,[],[f3])).
% 8.00/1.50  
% 8.00/1.50  fof(f47,plain,(
% 8.00/1.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f21])).
% 8.00/1.50  
% 8.00/1.50  fof(f73,plain,(
% 8.00/1.50    ( ! [X4,X5] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f75,plain,(
% 8.00/1.50    ( ! [X5] : (~m1_subset_1(sK3,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 8.00/1.50    inference(equality_resolution,[],[f73])).
% 8.00/1.50  
% 8.00/1.50  fof(f76,plain,(
% 8.00/1.50    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 8.00/1.50    inference(equality_resolution,[],[f75])).
% 8.00/1.50  
% 8.00/1.50  fof(f49,plain,(
% 8.00/1.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f38])).
% 8.00/1.50  
% 8.00/1.50  fof(f2,axiom,(
% 8.00/1.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f46,plain,(
% 8.00/1.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f2])).
% 8.00/1.50  
% 8.00/1.50  fof(f1,axiom,(
% 8.00/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f18,plain,(
% 8.00/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.00/1.50    inference(unused_predicate_definition_removal,[],[f1])).
% 8.00/1.50  
% 8.00/1.50  fof(f20,plain,(
% 8.00/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 8.00/1.50    inference(ennf_transformation,[],[f18])).
% 8.00/1.50  
% 8.00/1.50  fof(f45,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f20])).
% 8.00/1.50  
% 8.00/1.50  fof(f51,plain,(
% 8.00/1.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f38])).
% 8.00/1.50  
% 8.00/1.50  fof(f7,axiom,(
% 8.00/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f25,plain,(
% 8.00/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f7])).
% 8.00/1.50  
% 8.00/1.50  fof(f54,plain,(
% 8.00/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f25])).
% 8.00/1.50  
% 8.00/1.50  fof(f9,axiom,(
% 8.00/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f27,plain,(
% 8.00/1.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f9])).
% 8.00/1.50  
% 8.00/1.50  fof(f28,plain,(
% 8.00/1.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(flattening,[],[f27])).
% 8.00/1.50  
% 8.00/1.50  fof(f56,plain,(
% 8.00/1.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f28])).
% 8.00/1.50  
% 8.00/1.50  fof(f8,axiom,(
% 8.00/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f26,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f8])).
% 8.00/1.50  
% 8.00/1.50  fof(f55,plain,(
% 8.00/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f26])).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f50]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_21,negated_conjecture,
% 8.00/1.50      ( m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
% 8.00/1.50      inference(cnf_transformation,[],[f72]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6748,plain,
% 8.00/1.50      ( ~ v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
% 8.00/1.50      | v1_xboole_0(sK3) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_4,c_21]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_19,plain,
% 8.00/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.00/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.50      | ~ l1_pre_topc(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f64]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.00/1.50      | ~ r2_hidden(X2,X0)
% 8.00/1.50      | r2_hidden(X2,X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f52]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2428,plain,
% 8.00/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.00/1.50      | ~ r2_hidden(X2,u1_struct_0(X0))
% 8.00/1.50      | r2_hidden(X2,u1_struct_0(X1))
% 8.00/1.50      | ~ l1_pre_topc(X1) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_19,c_7]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f48]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1199,plain,
% 8.00/1.50      ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
% 8.00/1.50      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_6,c_21]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2598,plain,
% 8.00/1.50      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
% 8.00/1.50      | r2_hidden(sK3,u1_struct_0(X0))
% 8.00/1.50      | ~ l1_pre_topc(X0)
% 8.00/1.50      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_2428,c_1199]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_16,plain,
% 8.00/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.00/1.50      | ~ m1_pre_topc(X2,X1)
% 8.00/1.50      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 8.00/1.50      | v2_struct_0(X1)
% 8.00/1.50      | v2_struct_0(X2)
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | ~ l1_pre_topc(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f63]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5718,plain,
% 8.00/1.50      ( ~ m1_pre_topc(sK1,sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK2,sK0)
% 8.00/1.50      | r2_hidden(sK3,u1_struct_0(sK0))
% 8.00/1.50      | v2_struct_0(sK0)
% 8.00/1.50      | v2_struct_0(sK1)
% 8.00/1.50      | v2_struct_0(sK2)
% 8.00/1.50      | ~ l1_pre_topc(sK0)
% 8.00/1.50      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_2598,c_16]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_28,negated_conjecture,
% 8.00/1.50      ( ~ v2_struct_0(sK0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f65]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_27,negated_conjecture,
% 8.00/1.50      ( l1_pre_topc(sK0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f66]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_26,negated_conjecture,
% 8.00/1.50      ( ~ v2_struct_0(sK1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f67]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_25,negated_conjecture,
% 8.00/1.50      ( m1_pre_topc(sK1,sK0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f68]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_24,negated_conjecture,
% 8.00/1.50      ( ~ v2_struct_0(sK2) ),
% 8.00/1.50      inference(cnf_transformation,[],[f69]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_23,negated_conjecture,
% 8.00/1.50      ( m1_pre_topc(sK2,sK0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f70]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6543,plain,
% 8.00/1.50      ( r2_hidden(sK3,u1_struct_0(sK0))
% 8.00/1.50      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_5718,c_28,c_27,c_26,c_25,c_24,c_23]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6756,plain,
% 8.00/1.50      ( r2_hidden(sK3,u1_struct_0(sK0)) | v1_xboole_0(sK3) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_6748,c_6543]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6876,plain,
% 8.00/1.50      ( ~ m1_pre_topc(sK0,X0)
% 8.00/1.50      | r2_hidden(sK3,u1_struct_0(X0))
% 8.00/1.50      | ~ l1_pre_topc(X0)
% 8.00/1.50      | v1_xboole_0(sK3) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_6756,c_2428]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_784,plain,
% 8.00/1.50      ( m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_799,plain,
% 8.00/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 8.00/1.50      | r2_hidden(X0,X1) = iProver_top
% 8.00/1.50      | v1_xboole_0(X1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2108,plain,
% 8.00/1.50      ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top
% 8.00/1.50      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_784,c_799]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_782,plain,
% 8.00/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_780,plain,
% 8.00/1.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_15,plain,
% 8.00/1.50      ( r1_tsep_1(X0,X1)
% 8.00/1.50      | ~ m1_pre_topc(X0,X2)
% 8.00/1.50      | ~ m1_pre_topc(X1,X2)
% 8.00/1.50      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 8.00/1.50      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 8.00/1.50      | v2_struct_0(X2)
% 8.00/1.50      | v2_struct_0(X1)
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 8.00/1.50      | ~ l1_pre_topc(X2)
% 8.00/1.50      | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f74]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_790,plain,
% 8.00/1.50      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
% 8.00/1.50      | r1_tsep_1(X1,X2) = iProver_top
% 8.00/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 8.00/1.50      | m1_pre_topc(X2,X0) != iProver_top
% 8.00/1.50      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) != iProver_top
% 8.00/1.50      | v1_pre_topc(k2_tsep_1(X0,X1,X2)) != iProver_top
% 8.00/1.50      | v2_struct_0(X2) = iProver_top
% 8.00/1.50      | v2_struct_0(X0) = iProver_top
% 8.00/1.50      | v2_struct_0(X1) = iProver_top
% 8.00/1.50      | v2_struct_0(k2_tsep_1(X0,X1,X2)) = iProver_top
% 8.00/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18,plain,
% 8.00/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.00/1.50      | ~ m1_pre_topc(X2,X1)
% 8.00/1.50      | v2_struct_0(X1)
% 8.00/1.50      | v2_struct_0(X2)
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 8.00/1.50      | ~ l1_pre_topc(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f61]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_787,plain,
% 8.00/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.00/1.50      | m1_pre_topc(X2,X1) != iProver_top
% 8.00/1.50      | v2_struct_0(X1) = iProver_top
% 8.00/1.50      | v2_struct_0(X2) = iProver_top
% 8.00/1.50      | v2_struct_0(X0) = iProver_top
% 8.00/1.50      | v2_struct_0(k2_tsep_1(X1,X0,X2)) != iProver_top
% 8.00/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_17,plain,
% 8.00/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.00/1.50      | ~ m1_pre_topc(X2,X1)
% 8.00/1.50      | v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 8.00/1.50      | v2_struct_0(X1)
% 8.00/1.50      | v2_struct_0(X2)
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | ~ l1_pre_topc(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f62]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_788,plain,
% 8.00/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.00/1.50      | m1_pre_topc(X2,X1) != iProver_top
% 8.00/1.50      | v1_pre_topc(k2_tsep_1(X1,X0,X2)) = iProver_top
% 8.00/1.50      | v2_struct_0(X1) = iProver_top
% 8.00/1.50      | v2_struct_0(X2) = iProver_top
% 8.00/1.50      | v2_struct_0(X0) = iProver_top
% 8.00/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_789,plain,
% 8.00/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.00/1.50      | m1_pre_topc(X2,X1) != iProver_top
% 8.00/1.50      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1) = iProver_top
% 8.00/1.50      | v2_struct_0(X1) = iProver_top
% 8.00/1.50      | v2_struct_0(X2) = iProver_top
% 8.00/1.50      | v2_struct_0(X0) = iProver_top
% 8.00/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_982,plain,
% 8.00/1.50      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
% 8.00/1.50      | r1_tsep_1(X1,X2) = iProver_top
% 8.00/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 8.00/1.50      | m1_pre_topc(X2,X0) != iProver_top
% 8.00/1.50      | v2_struct_0(X1) = iProver_top
% 8.00/1.50      | v2_struct_0(X2) = iProver_top
% 8.00/1.50      | v2_struct_0(X0) = iProver_top
% 8.00/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.00/1.50      inference(forward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_790,c_787,c_788,c_789]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4812,plain,
% 8.00/1.50      ( u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
% 8.00/1.50      | r1_tsep_1(sK1,X0) = iProver_top
% 8.00/1.50      | m1_pre_topc(X0,sK0) != iProver_top
% 8.00/1.50      | v2_struct_0(X0) = iProver_top
% 8.00/1.50      | v2_struct_0(sK0) = iProver_top
% 8.00/1.50      | v2_struct_0(sK1) = iProver_top
% 8.00/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_780,c_982]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_29,plain,
% 8.00/1.50      ( v2_struct_0(sK0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_30,plain,
% 8.00/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_31,plain,
% 8.00/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6681,plain,
% 8.00/1.50      ( v2_struct_0(X0) = iProver_top
% 8.00/1.50      | m1_pre_topc(X0,sK0) != iProver_top
% 8.00/1.50      | r1_tsep_1(sK1,X0) = iProver_top
% 8.00/1.50      | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_4812,c_29,c_30,c_31]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6682,plain,
% 8.00/1.50      ( u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
% 8.00/1.50      | r1_tsep_1(sK1,X0) = iProver_top
% 8.00/1.50      | m1_pre_topc(X0,sK0) != iProver_top
% 8.00/1.50      | v2_struct_0(X0) = iProver_top ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_6681]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6692,plain,
% 8.00/1.50      ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 8.00/1.50      | r1_tsep_1(sK1,sK2) = iProver_top
% 8.00/1.50      | v2_struct_0(sK2) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_782,c_6682]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22,negated_conjecture,
% 8.00/1.50      ( ~ r1_tsep_1(sK1,sK2) ),
% 8.00/1.50      inference(cnf_transformation,[],[f71]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1129,plain,
% 8.00/1.50      ( ~ m1_pre_topc(X0,sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK2,sK0)
% 8.00/1.50      | v1_pre_topc(k2_tsep_1(sK0,X0,sK2))
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | v2_struct_0(sK0)
% 8.00/1.50      | v2_struct_0(sK2)
% 8.00/1.50      | ~ l1_pre_topc(sK0) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1267,plain,
% 8.00/1.50      ( ~ m1_pre_topc(sK1,sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK2,sK0)
% 8.00/1.50      | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
% 8.00/1.50      | v2_struct_0(sK0)
% 8.00/1.50      | v2_struct_0(sK1)
% 8.00/1.50      | v2_struct_0(sK2)
% 8.00/1.50      | ~ l1_pre_topc(sK0) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1129]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1161,plain,
% 8.00/1.50      ( ~ m1_pre_topc(X0,sK0)
% 8.00/1.50      | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK2,sK0)
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | v2_struct_0(sK0)
% 8.00/1.50      | v2_struct_0(sK2)
% 8.00/1.50      | ~ l1_pre_topc(sK0) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1296,plain,
% 8.00/1.50      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK1,sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK2,sK0)
% 8.00/1.50      | v2_struct_0(sK0)
% 8.00/1.50      | v2_struct_0(sK1)
% 8.00/1.50      | v2_struct_0(sK2)
% 8.00/1.50      | ~ l1_pre_topc(sK0) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1161]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1352,plain,
% 8.00/1.50      ( r1_tsep_1(sK1,sK2)
% 8.00/1.50      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK1,sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK2,sK0)
% 8.00/1.50      | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
% 8.00/1.50      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 8.00/1.50      | v2_struct_0(sK0)
% 8.00/1.50      | v2_struct_0(sK1)
% 8.00/1.50      | v2_struct_0(sK2)
% 8.00/1.50      | ~ l1_pre_topc(sK0)
% 8.00/1.50      | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1906,plain,
% 8.00/1.50      ( ~ m1_pre_topc(sK1,sK0)
% 8.00/1.50      | ~ m1_pre_topc(sK2,sK0)
% 8.00/1.50      | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 8.00/1.50      | v2_struct_0(sK0)
% 8.00/1.50      | v2_struct_0(sK1)
% 8.00/1.50      | v2_struct_0(sK2)
% 8.00/1.50      | ~ l1_pre_topc(sK0) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6824,plain,
% 8.00/1.50      ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_6692,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_1267,c_1296,
% 8.00/1.50                 c_1352,c_1906]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_786,plain,
% 8.00/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.00/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.00/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.00/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f53]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_797,plain,
% 8.00/1.50      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1974,plain,
% 8.00/1.50      ( k9_subset_1(u1_struct_0(X0),X1,u1_struct_0(X2)) = k3_xboole_0(X1,u1_struct_0(X2))
% 8.00/1.50      | m1_pre_topc(X2,X0) != iProver_top
% 8.00/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_786,c_797]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5190,plain,
% 8.00/1.50      ( k9_subset_1(u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2))
% 8.00/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_782,c_1974]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1090,plain,
% 8.00/1.50      ( ~ m1_pre_topc(sK2,sK0)
% 8.00/1.50      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.50      | ~ l1_pre_topc(sK0) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1220,plain,
% 8.00/1.50      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.50      | k9_subset_1(u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5224,plain,
% 8.00/1.50      ( k9_subset_1(u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_5190,c_27,c_23,c_1090,c_1220]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_13,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.50      | m1_subset_1(k9_subset_1(u1_struct_0(X1),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
% 8.00/1.50      | ~ l1_pre_topc(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f58]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_792,plain,
% 8.00/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.00/1.50      | m1_subset_1(k9_subset_1(u1_struct_0(X1),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))) = iProver_top
% 8.00/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5228,plain,
% 8.00/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.50      | m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))))) = iProver_top
% 8.00/1.50      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_5224,c_792]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_12,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.50      | ~ l1_pre_topc(X1)
% 8.00/1.50      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f57]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_793,plain,
% 8.00/1.50      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 8.00/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.00/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2920,plain,
% 8.00/1.50      ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1))) = u1_struct_0(X1)
% 8.00/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 8.00/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_786,c_793]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3743,plain,
% 8.00/1.50      ( u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) = u1_struct_0(sK2)
% 8.00/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_782,c_2920]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1230,plain,
% 8.00/1.50      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.50      | ~ l1_pre_topc(sK0)
% 8.00/1.50      | u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3930,plain,
% 8.00/1.50      ( u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_3743,c_27,c_23,c_1090,c_1230]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5229,plain,
% 8.00/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.50      | m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 8.00/1.50      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_5228,c_3930]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_34,plain,
% 8.00/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1091,plain,
% 8.00/1.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 8.00/1.50      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.00/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1090]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7961,plain,
% 8.00/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.50      | m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_5229,c_30,c_34,c_1091]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7969,plain,
% 8.00/1.50      ( m1_subset_1(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 8.00/1.50      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_6824,c_7961]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_32,plain,
% 8.00/1.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1093,plain,
% 8.00/1.50      ( ~ m1_pre_topc(sK1,sK0)
% 8.00/1.50      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.50      | ~ l1_pre_topc(sK0) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1094,plain,
% 8.00/1.50      ( m1_pre_topc(sK1,sK0) != iProver_top
% 8.00/1.50      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.00/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1093]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8034,plain,
% 8.00/1.50      ( m1_subset_1(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_7969,c_30,c_32,c_1094]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_798,plain,
% 8.00/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.00/1.50      | r2_hidden(X2,X0) != iProver_top
% 8.00/1.50      | r2_hidden(X2,X1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8041,plain,
% 8.00/1.50      ( r2_hidden(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != iProver_top
% 8.00/1.50      | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_8034,c_798]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8436,plain,
% 8.00/1.50      ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 8.00/1.50      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2108,c_8041]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_800,plain,
% 8.00/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 8.00/1.50      | v1_xboole_0(X1) != iProver_top
% 8.00/1.50      | v1_xboole_0(X0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2130,plain,
% 8.00/1.50      ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != iProver_top
% 8.00/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_784,c_800]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8893,plain,
% 8.00/1.50      ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 8.00/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_8436,c_2130]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2,plain,
% 8.00/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f47]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_802,plain,
% 8.00/1.50      ( r2_hidden(X0,X1) != iProver_top
% 8.00/1.50      | v1_xboole_0(X1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_9767,plain,
% 8.00/1.50      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_8893,c_802]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_20,negated_conjecture,
% 8.00/1.50      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 8.00/1.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f76]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5,plain,
% 8.00/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f49]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_208,plain,
% 8.00/1.50      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 8.00/1.50      inference(global_propositional_subsumption,[status(thm)],[c_5,c_2]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_209,plain,
% 8.00/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_208]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1759,plain,
% 8.00/1.50      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 8.00/1.50      | ~ r2_hidden(sK3,u1_struct_0(sK1)) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_20,c_209]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1760,plain,
% 8.00/1.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | r2_hidden(sK3,u1_struct_0(sK1)) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1,plain,
% 8.00/1.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f46]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_803,plain,
% 8.00/1.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6827,plain,
% 8.00/1.50      ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_6824,c_803]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_0,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f45]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_804,plain,
% 8.00/1.50      ( r1_tarski(X0,X1) != iProver_top
% 8.00/1.50      | r2_hidden(X2,X0) != iProver_top
% 8.00/1.50      | r2_hidden(X2,X1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2564,plain,
% 8.00/1.50      ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X0) != iProver_top
% 8.00/1.50      | r2_hidden(sK3,X0) = iProver_top
% 8.00/1.50      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
% 8.00/1.51      inference(superposition,[status(thm)],[c_2108,c_804]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_6939,plain,
% 8.00/1.51      ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
% 8.00/1.51      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = iProver_top ),
% 8.00/1.51      inference(superposition,[status(thm)],[c_6827,c_2564]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_776,plain,
% 8.00/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 8.00/1.51      | r2_hidden(X0,X1) != iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_9768,plain,
% 8.00/1.51      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top
% 8.00/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 8.00/1.51      inference(superposition,[status(thm)],[c_8893,c_776]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_10318,plain,
% 8.00/1.51      ( v1_xboole_0(sK3) = iProver_top ),
% 8.00/1.51      inference(global_propositional_subsumption,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_9767,c_1760,c_2130,c_6939,c_9768]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_10320,plain,
% 8.00/1.51      ( v1_xboole_0(sK3) ),
% 8.00/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_10318]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_28543,plain,
% 8.00/1.51      ( v1_xboole_0(sK3) ),
% 8.00/1.51      inference(global_propositional_subsumption,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_6876,c_10320]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_3,plain,
% 8.00/1.51      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 8.00/1.51      inference(cnf_transformation,[],[f51]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_6569,plain,
% 8.00/1.51      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 8.00/1.51      | ~ v1_xboole_0(u1_struct_0(sK1))
% 8.00/1.51      | ~ v1_xboole_0(sK3) ),
% 8.00/1.51      inference(resolution,[status(thm)],[c_3,c_20]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_28594,plain,
% 8.00/1.51      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 8.00/1.51      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 8.00/1.51      inference(backward_subsumption_resolution,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_28543,c_6569]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_9,plain,
% 8.00/1.51      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 8.00/1.51      inference(cnf_transformation,[],[f54]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_7003,plain,
% 8.00/1.51      ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
% 8.00/1.51      | l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_11,plain,
% 8.00/1.51      ( v2_struct_0(X0)
% 8.00/1.51      | ~ l1_struct_0(X0)
% 8.00/1.51      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 8.00/1.51      inference(cnf_transformation,[],[f56]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_794,plain,
% 8.00/1.51      ( v2_struct_0(X0) = iProver_top
% 8.00/1.51      | l1_struct_0(X0) != iProver_top
% 8.00/1.51      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_22433,plain,
% 8.00/1.51      ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
% 8.00/1.51      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
% 8.00/1.51      | l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 8.00/1.51      inference(superposition,[status(thm)],[c_6939,c_794]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_33,plain,
% 8.00/1.51      ( v2_struct_0(sK2) != iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1907,plain,
% 8.00/1.51      ( m1_pre_topc(sK1,sK0) != iProver_top
% 8.00/1.51      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.00/1.51      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 8.00/1.51      | v2_struct_0(sK0) = iProver_top
% 8.00/1.51      | v2_struct_0(sK1) = iProver_top
% 8.00/1.51      | v2_struct_0(sK2) = iProver_top
% 8.00/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_1906]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_22443,plain,
% 8.00/1.51      ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
% 8.00/1.51      | l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 8.00/1.51      inference(global_propositional_subsumption,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_22433,c_29,c_30,c_31,c_32,c_33,c_34,c_1907]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_22445,plain,
% 8.00/1.51      ( r2_hidden(sK3,u1_struct_0(sK1))
% 8.00/1.51      | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
% 8.00/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_22443]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_10,plain,
% 8.00/1.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 8.00/1.51      inference(cnf_transformation,[],[f55]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_24988,plain,
% 8.00/1.51      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
% 8.00/1.51      | ~ l1_pre_topc(X0)
% 8.00/1.51      | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_24990,plain,
% 8.00/1.51      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 8.00/1.51      | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
% 8.00/1.51      | ~ l1_pre_topc(sK0) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_24988]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_28598,plain,
% 8.00/1.51      ( ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.51      inference(global_propositional_subsumption,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_28594,c_28,c_27,c_26,c_25,c_24,c_23,c_1296,c_1759,
% 8.00/1.51                 c_7003,c_22445,c_24990]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_28610,plain,
% 8.00/1.51      ( ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
% 8.00/1.51      inference(resolution,[status(thm)],[c_28598,c_209]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_8892,plain,
% 8.00/1.51      ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 8.00/1.51      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
% 8.00/1.51      | l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 8.00/1.51      inference(superposition,[status(thm)],[c_8436,c_794]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_8904,plain,
% 8.00/1.51      ( r2_hidden(sK3,u1_struct_0(sK2))
% 8.00/1.51      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 8.00/1.51      | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
% 8.00/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_8892]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(contradiction,plain,
% 8.00/1.51      ( $false ),
% 8.00/1.51      inference(minisat,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_28610,c_24990,c_8904,c_7003,c_1906,c_1296,c_23,c_24,
% 8.00/1.51                 c_25,c_26,c_27,c_28]) ).
% 8.00/1.51  
% 8.00/1.51  
% 8.00/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 8.00/1.51  
% 8.00/1.51  ------                               Statistics
% 8.00/1.51  
% 8.00/1.51  ------ Selected
% 8.00/1.51  
% 8.00/1.51  total_time:                             0.943
% 8.00/1.51  
%------------------------------------------------------------------------------
