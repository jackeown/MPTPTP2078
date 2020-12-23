%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:54 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  324 (95611 expanded)
%              Number of clauses        :  203 (21330 expanded)
%              Number of leaves         :   30 (27296 expanded)
%              Depth                    :   37
%              Number of atoms          : 1453 (1014813 expanded)
%              Number of equality atoms :  591 (105470 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f66])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f61,f62])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f136,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f72,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f72])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | v5_pre_topc(X2,X0,X1) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
          & v1_funct_1(X3) )
     => ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK6 = X2
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | v5_pre_topc(X2,X0,X1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ v5_pre_topc(sK5,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK5,X0,X1) )
            & sK5 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
                  | ~ v5_pre_topc(X2,X0,sK4) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
                  | v5_pre_topc(X2,X0,sK4) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK3,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | ~ v5_pre_topc(sK5,sK3,sK4) )
    & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | v5_pre_topc(sK5,sK3,sK4) )
    & sK5 = sK6
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f73,f77,f76,f75,f74])).

fof(f130,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f78])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f128,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f78])).

fof(f129,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f78])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f135,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f142,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f109])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f64])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f138,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f91])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f146,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f117])).

fof(f121,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

fof(f122,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

fof(f123,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f124,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f133,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f131,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f78])).

fof(f126,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f78])).

fof(f132,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f127,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f78])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f116,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f114,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f115,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f147,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f145,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f148,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f119])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f137,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f92])).

cnf(c_24,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2965,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2973,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4434,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2965,c_2973])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2949,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_34,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_702,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_20,c_34])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_702,c_34,c_20,c_19])).

cnf(c_705,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_704])).

cnf(c_742,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_25,c_705])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_34,c_25,c_20,c_19])).

cnf(c_745,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_744])).

cnf(c_2938,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_3575,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_2938])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_62,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_63,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_3750,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3575,c_62,c_63])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2971,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_15,c_8])).

cnf(c_2939,plain,
    ( k3_xboole_0(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_3816,plain,
    ( k3_xboole_0(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = sK6 ),
    inference(superposition,[status(thm)],[c_2949,c_2939])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2974,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4464,plain,
    ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3816,c_2974])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2979,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4641,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4464,c_2979])).

cnf(c_4742,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_4641])).

cnf(c_4849,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3750,c_4742])).

cnf(c_11037,plain,
    ( k3_xboole_0(sK6,X0) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_4434,c_4849])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_139,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_138,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_140,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_2962,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2988,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2962,c_12])).

cnf(c_2995,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2988])).

cnf(c_2994,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2988])).

cnf(c_2996,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2994])).

cnf(c_1972,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_4921,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X2
    | u1_struct_0(sK3) != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_4923,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4921])).

cnf(c_2970,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2968,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4944,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2970,c_2968])).

cnf(c_18,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4949,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4944,c_18])).

cnf(c_4954,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4949])).

cnf(c_4077,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_2971])).

cnf(c_4305,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3750,c_4077])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2972,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4935,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3750,c_2972])).

cnf(c_5267,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_4305,c_4935])).

cnf(c_4356,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2965,c_2979])).

cnf(c_7789,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_4356])).

cnf(c_9017,plain,
    ( k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_3750,c_7789])).

cnf(c_39,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_2954,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5497,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_2954])).

cnf(c_54,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_55,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_53,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_56,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_57,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_58,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_64,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_42,negated_conjecture,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2951,plain,
    ( v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_44,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_2986,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2951,c_44])).

cnf(c_49,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2945,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_2982,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2945,c_44])).

cnf(c_43,negated_conjecture,
    ( v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_2950,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2985,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2950,c_44])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2946,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_2983,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2946,c_44])).

cnf(c_37,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3141,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_3142,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3141])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3373,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3374,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3373])).

cnf(c_36,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3565,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3566,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3565])).

cnf(c_40,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_3300,plain,
    ( ~ v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,X0,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_3878,plain,
    ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3300])).

cnf(c_3879,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3878])).

cnf(c_38,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_3517,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
    | v5_pre_topc(sK6,sK3,X0)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_3913,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3517])).

cnf(c_3914,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3913])).

cnf(c_41,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_3829,plain,
    ( ~ v5_pre_topc(sK6,sK3,X0)
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_5291,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3829])).

cnf(c_5292,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5291])).

cnf(c_5675,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5497,c_55,c_56,c_57,c_58,c_62,c_63,c_64,c_2986,c_2982,c_2985,c_2983,c_3142,c_3374,c_3566,c_3879,c_3914,c_5292])).

cnf(c_5676,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5675])).

cnf(c_5679,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5676,c_55,c_56,c_57,c_58,c_62,c_63,c_64,c_2982,c_2985,c_2983,c_3142,c_3374,c_3566,c_3914,c_5292])).

cnf(c_9795,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9017,c_5679])).

cnf(c_9794,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9017,c_2949])).

cnf(c_10392,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9795,c_9794])).

cnf(c_10393,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10392])).

cnf(c_10394,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10393])).

cnf(c_3817,plain,
    ( k3_xboole_0(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = sK6 ),
    inference(superposition,[status(thm)],[c_2983,c_2939])).

cnf(c_11027,plain,
    ( k3_xboole_0(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = k1_xboole_0
    | r2_hidden(sK2(sK6),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3817,c_4434])).

cnf(c_11043,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK6),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11027,c_3817])).

cnf(c_4861,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2965,c_4849])).

cnf(c_2948,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_9966,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4861,c_2948])).

cnf(c_3384,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_2938])).

cnf(c_3633,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3384,c_62,c_2982])).

cnf(c_4934,plain,
    ( u1_struct_0(sK4) = X0
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3633,c_2972])).

cnf(c_5261,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_3750,c_4934])).

cnf(c_5338,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5261,c_2948])).

cnf(c_2952,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4427,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_2952])).

cnf(c_3126,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_3127,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3126])).

cnf(c_3363,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3364,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3363])).

cnf(c_3542,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3543,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3542])).

cnf(c_3904,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3517])).

cnf(c_3905,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3904])).

cnf(c_4565,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_55,c_56,c_57,c_58,c_62,c_63,c_2986,c_2982,c_2983,c_3127,c_3364,c_3543,c_3905])).

cnf(c_4566,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4565])).

cnf(c_2953,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4865,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_2953])).

cnf(c_5169,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4865,c_55,c_56,c_57,c_58,c_62,c_63,c_2986,c_2982,c_2983,c_3127,c_3364,c_3543,c_3905,c_4427])).

cnf(c_5170,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5169])).

cnf(c_5173,plain,
    ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_5170])).

cnf(c_3802,plain,
    ( ~ v5_pre_topc(sK6,X0,sK4)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_5277,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3802])).

cnf(c_5278,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5277])).

cnf(c_5337,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5261,c_2949])).

cnf(c_5361,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5338,c_55,c_56,c_57,c_58,c_62,c_2982,c_2983,c_4566,c_5173,c_5278,c_5337])).

cnf(c_5362,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_5361])).

cnf(c_5372,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5362,c_4641])).

cnf(c_4465,plain,
    ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3817,c_2974])).

cnf(c_4636,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4465,c_2979])).

cnf(c_4737,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_4636])).

cnf(c_5858,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5372,c_3633,c_4737])).

cnf(c_5859,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_5858])).

cnf(c_5865,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2965,c_5859])).

cnf(c_9965,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4861,c_2949])).

cnf(c_7838,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5865,c_5679])).

cnf(c_10314,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9965,c_7838])).

cnf(c_10319,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5865,c_10314])).

cnf(c_11597,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11043,c_9966,c_10319])).

cnf(c_11664,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11597,c_3633])).

cnf(c_11673,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11664,c_18])).

cnf(c_12114,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11673,c_4356])).

cnf(c_7841,plain,
    ( sK6 = k1_xboole_0
    | v5_pre_topc(sK6,g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5865,c_5170])).

cnf(c_8411,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7841,c_55,c_56,c_57,c_58,c_62,c_63,c_2986,c_2982,c_2983,c_3127,c_3364,c_3543,c_3905,c_4427,c_5173,c_5278])).

cnf(c_8415,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5362,c_8411])).

cnf(c_8605,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5362,c_8415])).

cnf(c_11618,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK4)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11597,c_8605])).

cnf(c_11723,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11618,c_18])).

cnf(c_11724,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11723,c_12])).

cnf(c_13325,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11724,c_140])).

cnf(c_13326,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13325])).

cnf(c_17930,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12114,c_13326])).

cnf(c_19844,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11037,c_139,c_140,c_2995,c_2996,c_4923,c_4954,c_5267,c_9966,c_10319,c_10394,c_17930])).

cnf(c_5369,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(sK6)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5362,c_2952])).

cnf(c_6776,plain,
    ( l1_pre_topc(X1) != iProver_top
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(sK6)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5369,c_55,c_56])).

cnf(c_6777,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(sK6)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6776])).

cnf(c_6783,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_relat_1(sK6)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(sK6)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5362,c_6777])).

cnf(c_11633,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_relat_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(k1_xboole_0)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11597,c_6783])).

cnf(c_11699,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11633,c_18])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_11700,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11699,c_11])).

cnf(c_17907,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v5_pre_topc(X0,sK4,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK4,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12114,c_11700])).

cnf(c_17949,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v5_pre_topc(X0,sK4,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK4,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17907,c_12])).

cnf(c_18163,plain,
    ( u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17949,c_140,c_2995,c_4954,c_17930])).

cnf(c_19846,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19844,c_18,c_11597,c_18163])).

cnf(c_11668,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11597,c_2948])).

cnf(c_18188,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18163,c_11668])).

cnf(c_19849,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19846,c_18188])).

cnf(c_11646,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11597,c_5679])).

cnf(c_12492,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_11646])).

cnf(c_18175,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18163,c_12492])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19849,c_18175])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.73/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.49  
% 7.73/1.49  ------  iProver source info
% 7.73/1.49  
% 7.73/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.49  git: non_committed_changes: false
% 7.73/1.49  git: last_make_outside_of_git: false
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    ""
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.50  --prep_def_merge_mbd                    true
% 7.73/1.50  --prep_def_merge_tr_red                 false
% 7.73/1.50  --prep_def_merge_tr_cl                  false
% 7.73/1.50  --smt_preprocessing                     true
% 7.73/1.50  --smt_ac_axioms                         fast
% 7.73/1.50  --preprocessed_out                      false
% 7.73/1.50  --preprocessed_stats                    false
% 7.73/1.50  
% 7.73/1.50  ------ Abstraction refinement Options
% 7.73/1.50  
% 7.73/1.50  --abstr_ref                             []
% 7.73/1.50  --abstr_ref_prep                        false
% 7.73/1.50  --abstr_ref_until_sat                   false
% 7.73/1.50  --abstr_ref_sig_restrict                funpre
% 7.73/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.50  --abstr_ref_under                       []
% 7.73/1.50  
% 7.73/1.50  ------ SAT Options
% 7.73/1.50  
% 7.73/1.50  --sat_mode                              false
% 7.73/1.50  --sat_fm_restart_options                ""
% 7.73/1.50  --sat_gr_def                            false
% 7.73/1.50  --sat_epr_types                         true
% 7.73/1.50  --sat_non_cyclic_types                  false
% 7.73/1.50  --sat_finite_models                     false
% 7.73/1.50  --sat_fm_lemmas                         false
% 7.73/1.50  --sat_fm_prep                           false
% 7.73/1.50  --sat_fm_uc_incr                        true
% 7.73/1.50  --sat_out_model                         small
% 7.73/1.50  --sat_out_clauses                       false
% 7.73/1.50  
% 7.73/1.50  ------ QBF Options
% 7.73/1.50  
% 7.73/1.50  --qbf_mode                              false
% 7.73/1.50  --qbf_elim_univ                         false
% 7.73/1.50  --qbf_dom_inst                          none
% 7.73/1.50  --qbf_dom_pre_inst                      false
% 7.73/1.50  --qbf_sk_in                             false
% 7.73/1.50  --qbf_pred_elim                         true
% 7.73/1.50  --qbf_split                             512
% 7.73/1.50  
% 7.73/1.50  ------ BMC1 Options
% 7.73/1.50  
% 7.73/1.50  --bmc1_incremental                      false
% 7.73/1.50  --bmc1_axioms                           reachable_all
% 7.73/1.50  --bmc1_min_bound                        0
% 7.73/1.50  --bmc1_max_bound                        -1
% 7.73/1.50  --bmc1_max_bound_default                -1
% 7.73/1.50  --bmc1_symbol_reachability              true
% 7.73/1.50  --bmc1_property_lemmas                  false
% 7.73/1.50  --bmc1_k_induction                      false
% 7.73/1.50  --bmc1_non_equiv_states                 false
% 7.73/1.50  --bmc1_deadlock                         false
% 7.73/1.50  --bmc1_ucm                              false
% 7.73/1.50  --bmc1_add_unsat_core                   none
% 7.73/1.50  --bmc1_unsat_core_children              false
% 7.73/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.50  --bmc1_out_stat                         full
% 7.73/1.50  --bmc1_ground_init                      false
% 7.73/1.50  --bmc1_pre_inst_next_state              false
% 7.73/1.50  --bmc1_pre_inst_state                   false
% 7.73/1.50  --bmc1_pre_inst_reach_state             false
% 7.73/1.50  --bmc1_out_unsat_core                   false
% 7.73/1.50  --bmc1_aig_witness_out                  false
% 7.73/1.50  --bmc1_verbose                          false
% 7.73/1.50  --bmc1_dump_clauses_tptp                false
% 7.73/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.50  --bmc1_dump_file                        -
% 7.73/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.50  --bmc1_ucm_extend_mode                  1
% 7.73/1.50  --bmc1_ucm_init_mode                    2
% 7.73/1.50  --bmc1_ucm_cone_mode                    none
% 7.73/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.50  --bmc1_ucm_relax_model                  4
% 7.73/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.50  --bmc1_ucm_layered_model                none
% 7.73/1.50  --bmc1_ucm_max_lemma_size               10
% 7.73/1.50  
% 7.73/1.50  ------ AIG Options
% 7.73/1.50  
% 7.73/1.50  --aig_mode                              false
% 7.73/1.50  
% 7.73/1.50  ------ Instantiation Options
% 7.73/1.50  
% 7.73/1.50  --instantiation_flag                    true
% 7.73/1.50  --inst_sos_flag                         true
% 7.73/1.50  --inst_sos_phase                        true
% 7.73/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.50  --inst_lit_sel_side                     num_symb
% 7.73/1.50  --inst_solver_per_active                1400
% 7.73/1.50  --inst_solver_calls_frac                1.
% 7.73/1.50  --inst_passive_queue_type               priority_queues
% 7.73/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.50  --inst_passive_queues_freq              [25;2]
% 7.73/1.50  --inst_dismatching                      true
% 7.73/1.50  --inst_eager_unprocessed_to_passive     true
% 7.73/1.50  --inst_prop_sim_given                   true
% 7.73/1.50  --inst_prop_sim_new                     false
% 7.73/1.50  --inst_subs_new                         false
% 7.73/1.50  --inst_eq_res_simp                      false
% 7.73/1.50  --inst_subs_given                       false
% 7.73/1.50  --inst_orphan_elimination               true
% 7.73/1.50  --inst_learning_loop_flag               true
% 7.73/1.50  --inst_learning_start                   3000
% 7.73/1.50  --inst_learning_factor                  2
% 7.73/1.50  --inst_start_prop_sim_after_learn       3
% 7.73/1.50  --inst_sel_renew                        solver
% 7.73/1.50  --inst_lit_activity_flag                true
% 7.73/1.50  --inst_restr_to_given                   false
% 7.73/1.50  --inst_activity_threshold               500
% 7.73/1.50  --inst_out_proof                        true
% 7.73/1.50  
% 7.73/1.50  ------ Resolution Options
% 7.73/1.50  
% 7.73/1.50  --resolution_flag                       true
% 7.73/1.50  --res_lit_sel                           adaptive
% 7.73/1.50  --res_lit_sel_side                      none
% 7.73/1.50  --res_ordering                          kbo
% 7.73/1.50  --res_to_prop_solver                    active
% 7.73/1.50  --res_prop_simpl_new                    false
% 7.73/1.50  --res_prop_simpl_given                  true
% 7.73/1.50  --res_passive_queue_type                priority_queues
% 7.73/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.50  --res_passive_queues_freq               [15;5]
% 7.73/1.50  --res_forward_subs                      full
% 7.73/1.50  --res_backward_subs                     full
% 7.73/1.50  --res_forward_subs_resolution           true
% 7.73/1.50  --res_backward_subs_resolution          true
% 7.73/1.50  --res_orphan_elimination                true
% 7.73/1.50  --res_time_limit                        2.
% 7.73/1.50  --res_out_proof                         true
% 7.73/1.50  
% 7.73/1.50  ------ Superposition Options
% 7.73/1.50  
% 7.73/1.50  --superposition_flag                    true
% 7.73/1.50  --sup_passive_queue_type                priority_queues
% 7.73/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.50  --demod_completeness_check              fast
% 7.73/1.50  --demod_use_ground                      true
% 7.73/1.50  --sup_to_prop_solver                    passive
% 7.73/1.50  --sup_prop_simpl_new                    true
% 7.73/1.50  --sup_prop_simpl_given                  true
% 7.73/1.50  --sup_fun_splitting                     true
% 7.73/1.50  --sup_smt_interval                      50000
% 7.73/1.50  
% 7.73/1.50  ------ Superposition Simplification Setup
% 7.73/1.50  
% 7.73/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.50  --sup_immed_triv                        [TrivRules]
% 7.73/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_immed_bw_main                     []
% 7.73/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_input_bw                          []
% 7.73/1.50  
% 7.73/1.50  ------ Combination Options
% 7.73/1.50  
% 7.73/1.50  --comb_res_mult                         3
% 7.73/1.50  --comb_sup_mult                         2
% 7.73/1.50  --comb_inst_mult                        10
% 7.73/1.50  
% 7.73/1.50  ------ Debug Options
% 7.73/1.50  
% 7.73/1.50  --dbg_backtrace                         false
% 7.73/1.50  --dbg_dump_prop_clauses                 false
% 7.73/1.50  --dbg_dump_prop_clauses_file            -
% 7.73/1.50  --dbg_out_stat                          false
% 7.73/1.50  ------ Parsing...
% 7.73/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  ------ Proving...
% 7.73/1.50  ------ Problem Properties 
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  clauses                                 49
% 7.73/1.50  conjectures                             13
% 7.73/1.50  EPR                                     9
% 7.73/1.50  Horn                                    38
% 7.73/1.50  unary                                   16
% 7.73/1.50  binary                                  12
% 7.73/1.50  lits                                    141
% 7.73/1.50  lits eq                                 29
% 7.73/1.50  fd_pure                                 0
% 7.73/1.50  fd_pseudo                               0
% 7.73/1.50  fd_cond                                 7
% 7.73/1.50  fd_pseudo_cond                          5
% 7.73/1.50  AC symbols                              0
% 7.73/1.50  
% 7.73/1.50  ------ Schedule dynamic 5 is on 
% 7.73/1.50  
% 7.73/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ 
% 7.73/1.50  Current options:
% 7.73/1.50  ------ 
% 7.73/1.50  
% 7.73/1.50  ------ Input Options
% 7.73/1.50  
% 7.73/1.50  --out_options                           all
% 7.73/1.50  --tptp_safe_out                         true
% 7.73/1.50  --problem_path                          ""
% 7.73/1.50  --include_path                          ""
% 7.73/1.50  --clausifier                            res/vclausify_rel
% 7.73/1.50  --clausifier_options                    ""
% 7.73/1.50  --stdin                                 false
% 7.73/1.50  --stats_out                             all
% 7.73/1.50  
% 7.73/1.50  ------ General Options
% 7.73/1.50  
% 7.73/1.50  --fof                                   false
% 7.73/1.50  --time_out_real                         305.
% 7.73/1.50  --time_out_virtual                      -1.
% 7.73/1.50  --symbol_type_check                     false
% 7.73/1.50  --clausify_out                          false
% 7.73/1.50  --sig_cnt_out                           false
% 7.73/1.50  --trig_cnt_out                          false
% 7.73/1.50  --trig_cnt_out_tolerance                1.
% 7.73/1.50  --trig_cnt_out_sk_spl                   false
% 7.73/1.50  --abstr_cl_out                          false
% 7.73/1.50  
% 7.73/1.50  ------ Global Options
% 7.73/1.50  
% 7.73/1.50  --schedule                              default
% 7.73/1.50  --add_important_lit                     false
% 7.73/1.50  --prop_solver_per_cl                    1000
% 7.73/1.50  --min_unsat_core                        false
% 7.73/1.50  --soft_assumptions                      false
% 7.73/1.50  --soft_lemma_size                       3
% 7.73/1.50  --prop_impl_unit_size                   0
% 7.73/1.50  --prop_impl_unit                        []
% 7.73/1.50  --share_sel_clauses                     true
% 7.73/1.50  --reset_solvers                         false
% 7.73/1.50  --bc_imp_inh                            [conj_cone]
% 7.73/1.50  --conj_cone_tolerance                   3.
% 7.73/1.50  --extra_neg_conj                        none
% 7.73/1.50  --large_theory_mode                     true
% 7.73/1.50  --prolific_symb_bound                   200
% 7.73/1.50  --lt_threshold                          2000
% 7.73/1.50  --clause_weak_htbl                      true
% 7.73/1.50  --gc_record_bc_elim                     false
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing Options
% 7.73/1.50  
% 7.73/1.50  --preprocessing_flag                    true
% 7.73/1.50  --time_out_prep_mult                    0.1
% 7.73/1.50  --splitting_mode                        input
% 7.73/1.50  --splitting_grd                         true
% 7.73/1.50  --splitting_cvd                         false
% 7.73/1.50  --splitting_cvd_svl                     false
% 7.73/1.50  --splitting_nvd                         32
% 7.73/1.50  --sub_typing                            true
% 7.73/1.50  --prep_gs_sim                           true
% 7.73/1.50  --prep_unflatten                        true
% 7.73/1.50  --prep_res_sim                          true
% 7.73/1.50  --prep_upred                            true
% 7.73/1.50  --prep_sem_filter                       exhaustive
% 7.73/1.50  --prep_sem_filter_out                   false
% 7.73/1.50  --pred_elim                             true
% 7.73/1.50  --res_sim_input                         true
% 7.73/1.50  --eq_ax_congr_red                       true
% 7.73/1.50  --pure_diseq_elim                       true
% 7.73/1.50  --brand_transform                       false
% 7.73/1.50  --non_eq_to_eq                          false
% 7.73/1.50  --prep_def_merge                        true
% 7.73/1.50  --prep_def_merge_prop_impl              false
% 7.73/1.50  --prep_def_merge_mbd                    true
% 7.73/1.50  --prep_def_merge_tr_red                 false
% 7.73/1.50  --prep_def_merge_tr_cl                  false
% 7.73/1.50  --smt_preprocessing                     true
% 7.73/1.50  --smt_ac_axioms                         fast
% 7.73/1.50  --preprocessed_out                      false
% 7.73/1.50  --preprocessed_stats                    false
% 7.73/1.50  
% 7.73/1.50  ------ Abstraction refinement Options
% 7.73/1.50  
% 7.73/1.50  --abstr_ref                             []
% 7.73/1.50  --abstr_ref_prep                        false
% 7.73/1.50  --abstr_ref_until_sat                   false
% 7.73/1.50  --abstr_ref_sig_restrict                funpre
% 7.73/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.50  --abstr_ref_under                       []
% 7.73/1.50  
% 7.73/1.50  ------ SAT Options
% 7.73/1.50  
% 7.73/1.50  --sat_mode                              false
% 7.73/1.50  --sat_fm_restart_options                ""
% 7.73/1.50  --sat_gr_def                            false
% 7.73/1.50  --sat_epr_types                         true
% 7.73/1.50  --sat_non_cyclic_types                  false
% 7.73/1.50  --sat_finite_models                     false
% 7.73/1.50  --sat_fm_lemmas                         false
% 7.73/1.50  --sat_fm_prep                           false
% 7.73/1.50  --sat_fm_uc_incr                        true
% 7.73/1.50  --sat_out_model                         small
% 7.73/1.50  --sat_out_clauses                       false
% 7.73/1.50  
% 7.73/1.50  ------ QBF Options
% 7.73/1.50  
% 7.73/1.50  --qbf_mode                              false
% 7.73/1.50  --qbf_elim_univ                         false
% 7.73/1.50  --qbf_dom_inst                          none
% 7.73/1.50  --qbf_dom_pre_inst                      false
% 7.73/1.50  --qbf_sk_in                             false
% 7.73/1.50  --qbf_pred_elim                         true
% 7.73/1.50  --qbf_split                             512
% 7.73/1.50  
% 7.73/1.50  ------ BMC1 Options
% 7.73/1.50  
% 7.73/1.50  --bmc1_incremental                      false
% 7.73/1.50  --bmc1_axioms                           reachable_all
% 7.73/1.50  --bmc1_min_bound                        0
% 7.73/1.50  --bmc1_max_bound                        -1
% 7.73/1.50  --bmc1_max_bound_default                -1
% 7.73/1.50  --bmc1_symbol_reachability              true
% 7.73/1.50  --bmc1_property_lemmas                  false
% 7.73/1.50  --bmc1_k_induction                      false
% 7.73/1.50  --bmc1_non_equiv_states                 false
% 7.73/1.50  --bmc1_deadlock                         false
% 7.73/1.50  --bmc1_ucm                              false
% 7.73/1.50  --bmc1_add_unsat_core                   none
% 7.73/1.50  --bmc1_unsat_core_children              false
% 7.73/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.50  --bmc1_out_stat                         full
% 7.73/1.50  --bmc1_ground_init                      false
% 7.73/1.50  --bmc1_pre_inst_next_state              false
% 7.73/1.50  --bmc1_pre_inst_state                   false
% 7.73/1.50  --bmc1_pre_inst_reach_state             false
% 7.73/1.50  --bmc1_out_unsat_core                   false
% 7.73/1.50  --bmc1_aig_witness_out                  false
% 7.73/1.50  --bmc1_verbose                          false
% 7.73/1.50  --bmc1_dump_clauses_tptp                false
% 7.73/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.50  --bmc1_dump_file                        -
% 7.73/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.50  --bmc1_ucm_extend_mode                  1
% 7.73/1.50  --bmc1_ucm_init_mode                    2
% 7.73/1.50  --bmc1_ucm_cone_mode                    none
% 7.73/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.50  --bmc1_ucm_relax_model                  4
% 7.73/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.50  --bmc1_ucm_layered_model                none
% 7.73/1.50  --bmc1_ucm_max_lemma_size               10
% 7.73/1.50  
% 7.73/1.50  ------ AIG Options
% 7.73/1.50  
% 7.73/1.50  --aig_mode                              false
% 7.73/1.50  
% 7.73/1.50  ------ Instantiation Options
% 7.73/1.50  
% 7.73/1.50  --instantiation_flag                    true
% 7.73/1.50  --inst_sos_flag                         true
% 7.73/1.50  --inst_sos_phase                        true
% 7.73/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.50  --inst_lit_sel_side                     none
% 7.73/1.50  --inst_solver_per_active                1400
% 7.73/1.50  --inst_solver_calls_frac                1.
% 7.73/1.50  --inst_passive_queue_type               priority_queues
% 7.73/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.50  --inst_passive_queues_freq              [25;2]
% 7.73/1.50  --inst_dismatching                      true
% 7.73/1.50  --inst_eager_unprocessed_to_passive     true
% 7.73/1.50  --inst_prop_sim_given                   true
% 7.73/1.50  --inst_prop_sim_new                     false
% 7.73/1.50  --inst_subs_new                         false
% 7.73/1.50  --inst_eq_res_simp                      false
% 7.73/1.50  --inst_subs_given                       false
% 7.73/1.50  --inst_orphan_elimination               true
% 7.73/1.50  --inst_learning_loop_flag               true
% 7.73/1.50  --inst_learning_start                   3000
% 7.73/1.50  --inst_learning_factor                  2
% 7.73/1.50  --inst_start_prop_sim_after_learn       3
% 7.73/1.50  --inst_sel_renew                        solver
% 7.73/1.50  --inst_lit_activity_flag                true
% 7.73/1.50  --inst_restr_to_given                   false
% 7.73/1.50  --inst_activity_threshold               500
% 7.73/1.50  --inst_out_proof                        true
% 7.73/1.50  
% 7.73/1.50  ------ Resolution Options
% 7.73/1.50  
% 7.73/1.50  --resolution_flag                       false
% 7.73/1.50  --res_lit_sel                           adaptive
% 7.73/1.50  --res_lit_sel_side                      none
% 7.73/1.50  --res_ordering                          kbo
% 7.73/1.50  --res_to_prop_solver                    active
% 7.73/1.50  --res_prop_simpl_new                    false
% 7.73/1.50  --res_prop_simpl_given                  true
% 7.73/1.50  --res_passive_queue_type                priority_queues
% 7.73/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.50  --res_passive_queues_freq               [15;5]
% 7.73/1.50  --res_forward_subs                      full
% 7.73/1.50  --res_backward_subs                     full
% 7.73/1.50  --res_forward_subs_resolution           true
% 7.73/1.50  --res_backward_subs_resolution          true
% 7.73/1.50  --res_orphan_elimination                true
% 7.73/1.50  --res_time_limit                        2.
% 7.73/1.50  --res_out_proof                         true
% 7.73/1.50  
% 7.73/1.50  ------ Superposition Options
% 7.73/1.50  
% 7.73/1.50  --superposition_flag                    true
% 7.73/1.50  --sup_passive_queue_type                priority_queues
% 7.73/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.50  --demod_completeness_check              fast
% 7.73/1.50  --demod_use_ground                      true
% 7.73/1.50  --sup_to_prop_solver                    passive
% 7.73/1.50  --sup_prop_simpl_new                    true
% 7.73/1.50  --sup_prop_simpl_given                  true
% 7.73/1.50  --sup_fun_splitting                     true
% 7.73/1.50  --sup_smt_interval                      50000
% 7.73/1.50  
% 7.73/1.50  ------ Superposition Simplification Setup
% 7.73/1.50  
% 7.73/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.50  --sup_immed_triv                        [TrivRules]
% 7.73/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_immed_bw_main                     []
% 7.73/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_input_bw                          []
% 7.73/1.50  
% 7.73/1.50  ------ Combination Options
% 7.73/1.50  
% 7.73/1.50  --comb_res_mult                         3
% 7.73/1.50  --comb_sup_mult                         2
% 7.73/1.50  --comb_inst_mult                        10
% 7.73/1.50  
% 7.73/1.50  ------ Debug Options
% 7.73/1.50  
% 7.73/1.50  --dbg_backtrace                         false
% 7.73/1.50  --dbg_dump_prop_clauses                 false
% 7.73/1.50  --dbg_dump_prop_clauses_file            -
% 7.73/1.50  --dbg_out_stat                          false
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS status Theorem for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  fof(f14,axiom,(
% 7.73/1.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f38,plain,(
% 7.73/1.50    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 7.73/1.50    inference(ennf_transformation,[],[f14])).
% 7.73/1.50  
% 7.73/1.50  fof(f66,plain,(
% 7.73/1.50    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f67,plain,(
% 7.73/1.50    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f66])).
% 7.73/1.50  
% 7.73/1.50  fof(f101,plain,(
% 7.73/1.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 7.73/1.50    inference(cnf_transformation,[],[f67])).
% 7.73/1.50  
% 7.73/1.50  fof(f2,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f59,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(nnf_transformation,[],[f2])).
% 7.73/1.50  
% 7.73/1.50  fof(f60,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(flattening,[],[f59])).
% 7.73/1.50  
% 7.73/1.50  fof(f61,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(rectify,[],[f60])).
% 7.73/1.50  
% 7.73/1.50  fof(f62,plain,(
% 7.73/1.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f63,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f61,f62])).
% 7.73/1.50  
% 7.73/1.50  fof(f81,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.73/1.50    inference(cnf_transformation,[],[f63])).
% 7.73/1.50  
% 7.73/1.50  fof(f136,plain,(
% 7.73/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.73/1.50    inference(equality_resolution,[],[f81])).
% 7.73/1.50  
% 7.73/1.50  fof(f23,conjecture,(
% 7.73/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f24,negated_conjecture,(
% 7.73/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.73/1.50    inference(negated_conjecture,[],[f23])).
% 7.73/1.50  
% 7.73/1.50  fof(f53,plain,(
% 7.73/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f24])).
% 7.73/1.50  
% 7.73/1.50  fof(f54,plain,(
% 7.73/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.73/1.50    inference(flattening,[],[f53])).
% 7.73/1.50  
% 7.73/1.50  fof(f72,plain,(
% 7.73/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.73/1.50    inference(nnf_transformation,[],[f54])).
% 7.73/1.50  
% 7.73/1.50  fof(f73,plain,(
% 7.73/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.73/1.50    inference(flattening,[],[f72])).
% 7.73/1.50  
% 7.73/1.50  fof(f77,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK6 = X2 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK6))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f76,plain,(
% 7.73/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK5,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK5,X0,X1)) & sK5 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f75,plain,(
% 7.73/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(X2,X0,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(X2,X0,sK4)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f74,plain,(
% 7.73/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK3,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f78,plain,(
% 7.73/1.50    ((((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f73,f77,f76,f75,f74])).
% 7.73/1.50  
% 7.73/1.50  fof(f130,plain,(
% 7.73/1.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f15,axiom,(
% 7.73/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f39,plain,(
% 7.73/1.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.73/1.50    inference(ennf_transformation,[],[f15])).
% 7.73/1.50  
% 7.73/1.50  fof(f40,plain,(
% 7.73/1.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.73/1.50    inference(flattening,[],[f39])).
% 7.73/1.50  
% 7.73/1.50  fof(f105,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f40])).
% 7.73/1.50  
% 7.73/1.50  fof(f12,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f28,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.73/1.50    inference(pure_predicate_removal,[],[f12])).
% 7.73/1.50  
% 7.73/1.50  fof(f36,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(ennf_transformation,[],[f28])).
% 7.73/1.50  
% 7.73/1.50  fof(f99,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f36])).
% 7.73/1.50  
% 7.73/1.50  fof(f17,axiom,(
% 7.73/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f43,plain,(
% 7.73/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.73/1.50    inference(ennf_transformation,[],[f17])).
% 7.73/1.50  
% 7.73/1.50  fof(f44,plain,(
% 7.73/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.73/1.50    inference(flattening,[],[f43])).
% 7.73/1.50  
% 7.73/1.50  fof(f69,plain,(
% 7.73/1.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.73/1.50    inference(nnf_transformation,[],[f44])).
% 7.73/1.50  
% 7.73/1.50  fof(f112,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f69])).
% 7.73/1.50  
% 7.73/1.50  fof(f11,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f35,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(ennf_transformation,[],[f11])).
% 7.73/1.50  
% 7.73/1.50  fof(f98,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f35])).
% 7.73/1.50  
% 7.73/1.50  fof(f128,plain,(
% 7.73/1.50    v1_funct_1(sK6)),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f129,plain,(
% 7.73/1.50    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f5,axiom,(
% 7.73/1.50    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f31,plain,(
% 7.73/1.50    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 7.73/1.50    inference(ennf_transformation,[],[f5])).
% 7.73/1.50  
% 7.73/1.50  fof(f89,plain,(
% 7.73/1.50    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f31])).
% 7.73/1.50  
% 7.73/1.50  fof(f8,axiom,(
% 7.73/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f25,plain,(
% 7.73/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 7.73/1.50    inference(unused_predicate_definition_removal,[],[f8])).
% 7.73/1.50  
% 7.73/1.50  fof(f32,plain,(
% 7.73/1.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.73/1.50    inference(ennf_transformation,[],[f25])).
% 7.73/1.50  
% 7.73/1.50  fof(f94,plain,(
% 7.73/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f32])).
% 7.73/1.50  
% 7.73/1.50  fof(f3,axiom,(
% 7.73/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f29,plain,(
% 7.73/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.73/1.50    inference(ennf_transformation,[],[f3])).
% 7.73/1.50  
% 7.73/1.50  fof(f87,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f29])).
% 7.73/1.50  
% 7.73/1.50  fof(f82,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.73/1.50    inference(cnf_transformation,[],[f63])).
% 7.73/1.50  
% 7.73/1.50  fof(f135,plain,(
% 7.73/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.73/1.50    inference(equality_resolution,[],[f82])).
% 7.73/1.50  
% 7.73/1.50  fof(f1,axiom,(
% 7.73/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f55,plain,(
% 7.73/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.50    inference(nnf_transformation,[],[f1])).
% 7.73/1.50  
% 7.73/1.50  fof(f56,plain,(
% 7.73/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.50    inference(rectify,[],[f55])).
% 7.73/1.50  
% 7.73/1.50  fof(f57,plain,(
% 7.73/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f58,plain,(
% 7.73/1.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).
% 7.73/1.50  
% 7.73/1.50  fof(f79,plain,(
% 7.73/1.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f58])).
% 7.73/1.50  
% 7.73/1.50  fof(f7,axiom,(
% 7.73/1.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f93,plain,(
% 7.73/1.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f7])).
% 7.73/1.50  
% 7.73/1.50  fof(f16,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f41,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(ennf_transformation,[],[f16])).
% 7.73/1.50  
% 7.73/1.50  fof(f42,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(flattening,[],[f41])).
% 7.73/1.50  
% 7.73/1.50  fof(f68,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(nnf_transformation,[],[f42])).
% 7.73/1.50  
% 7.73/1.50  fof(f109,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f68])).
% 7.73/1.50  
% 7.73/1.50  fof(f142,plain,(
% 7.73/1.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.73/1.50    inference(equality_resolution,[],[f109])).
% 7.73/1.50  
% 7.73/1.50  fof(f6,axiom,(
% 7.73/1.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f64,plain,(
% 7.73/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.73/1.50    inference(nnf_transformation,[],[f6])).
% 7.73/1.50  
% 7.73/1.50  fof(f65,plain,(
% 7.73/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.73/1.50    inference(flattening,[],[f64])).
% 7.73/1.50  
% 7.73/1.50  fof(f91,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 7.73/1.50    inference(cnf_transformation,[],[f65])).
% 7.73/1.50  
% 7.73/1.50  fof(f138,plain,(
% 7.73/1.50    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 7.73/1.50    inference(equality_resolution,[],[f91])).
% 7.73/1.50  
% 7.73/1.50  fof(f13,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f37,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(ennf_transformation,[],[f13])).
% 7.73/1.50  
% 7.73/1.50  fof(f100,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f37])).
% 7.73/1.50  
% 7.73/1.50  fof(f10,axiom,(
% 7.73/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f96,plain,(
% 7.73/1.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.73/1.50    inference(cnf_transformation,[],[f10])).
% 7.73/1.50  
% 7.73/1.50  fof(f4,axiom,(
% 7.73/1.50    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f30,plain,(
% 7.73/1.50    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f4])).
% 7.73/1.50  
% 7.73/1.50  fof(f88,plain,(
% 7.73/1.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f30])).
% 7.73/1.50  
% 7.73/1.50  fof(f21,axiom,(
% 7.73/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f49,plain,(
% 7.73/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f21])).
% 7.73/1.50  
% 7.73/1.50  fof(f50,plain,(
% 7.73/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.50    inference(flattening,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f70,plain,(
% 7.73/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.50    inference(nnf_transformation,[],[f50])).
% 7.73/1.50  
% 7.73/1.50  fof(f117,plain,(
% 7.73/1.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f70])).
% 7.73/1.50  
% 7.73/1.50  fof(f146,plain,(
% 7.73/1.50    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(equality_resolution,[],[f117])).
% 7.73/1.50  
% 7.73/1.50  fof(f121,plain,(
% 7.73/1.50    v2_pre_topc(sK3)),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f122,plain,(
% 7.73/1.50    l1_pre_topc(sK3)),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f123,plain,(
% 7.73/1.50    v2_pre_topc(sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f124,plain,(
% 7.73/1.50    l1_pre_topc(sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f133,plain,(
% 7.73/1.50    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f131,plain,(
% 7.73/1.50    sK5 = sK6),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f126,plain,(
% 7.73/1.50    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f132,plain,(
% 7.73/1.50    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f127,plain,(
% 7.73/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 7.73/1.50    inference(cnf_transformation,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f20,axiom,(
% 7.73/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f26,plain,(
% 7.73/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.73/1.50    inference(pure_predicate_removal,[],[f20])).
% 7.73/1.50  
% 7.73/1.50  fof(f47,plain,(
% 7.73/1.50    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f26])).
% 7.73/1.50  
% 7.73/1.50  fof(f48,plain,(
% 7.73/1.50    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.50    inference(flattening,[],[f47])).
% 7.73/1.50  
% 7.73/1.50  fof(f116,plain,(
% 7.73/1.50    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f48])).
% 7.73/1.50  
% 7.73/1.50  fof(f18,axiom,(
% 7.73/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f27,plain,(
% 7.73/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.73/1.50    inference(pure_predicate_removal,[],[f18])).
% 7.73/1.50  
% 7.73/1.50  fof(f45,plain,(
% 7.73/1.50    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.73/1.50    inference(ennf_transformation,[],[f27])).
% 7.73/1.50  
% 7.73/1.50  fof(f114,plain,(
% 7.73/1.50    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f45])).
% 7.73/1.50  
% 7.73/1.50  fof(f19,axiom,(
% 7.73/1.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f46,plain,(
% 7.73/1.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f19])).
% 7.73/1.50  
% 7.73/1.50  fof(f115,plain,(
% 7.73/1.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f46])).
% 7.73/1.50  
% 7.73/1.50  fof(f22,axiom,(
% 7.73/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f51,plain,(
% 7.73/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f22])).
% 7.73/1.50  
% 7.73/1.50  fof(f52,plain,(
% 7.73/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.50    inference(flattening,[],[f51])).
% 7.73/1.50  
% 7.73/1.50  fof(f71,plain,(
% 7.73/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.50    inference(nnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f120,plain,(
% 7.73/1.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f71])).
% 7.73/1.50  
% 7.73/1.50  fof(f147,plain,(
% 7.73/1.50    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(equality_resolution,[],[f120])).
% 7.73/1.50  
% 7.73/1.50  fof(f118,plain,(
% 7.73/1.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f70])).
% 7.73/1.50  
% 7.73/1.50  fof(f145,plain,(
% 7.73/1.50    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(equality_resolution,[],[f118])).
% 7.73/1.50  
% 7.73/1.50  fof(f119,plain,(
% 7.73/1.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f71])).
% 7.73/1.50  
% 7.73/1.50  fof(f148,plain,(
% 7.73/1.50    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.50    inference(equality_resolution,[],[f119])).
% 7.73/1.50  
% 7.73/1.50  fof(f92,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 7.73/1.50    inference(cnf_transformation,[],[f65])).
% 7.73/1.50  
% 7.73/1.50  fof(f137,plain,(
% 7.73/1.50    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.73/1.50    inference(equality_resolution,[],[f92])).
% 7.73/1.50  
% 7.73/1.50  cnf(c_24,plain,
% 7.73/1.50      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2965,plain,
% 7.73/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_7,plain,
% 7.73/1.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f136]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2973,plain,
% 7.73/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.73/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4434,plain,
% 7.73/1.50      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 7.73/1.50      | r2_hidden(sK2(k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2965,c_2973]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_45,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f130]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2949,plain,
% 7.73/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_25,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | v1_partfun1(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | v1_xboole_0(X2) ),
% 7.73/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_20,plain,
% 7.73/1.50      ( v4_relat_1(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_34,plain,
% 7.73/1.50      ( ~ v1_partfun1(X0,X1)
% 7.73/1.50      | ~ v4_relat_1(X0,X1)
% 7.73/1.50      | ~ v1_relat_1(X0)
% 7.73/1.50      | k1_relat_1(X0) = X1 ),
% 7.73/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_702,plain,
% 7.73/1.50      ( ~ v1_partfun1(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ v1_relat_1(X0)
% 7.73/1.50      | k1_relat_1(X0) = X1 ),
% 7.73/1.50      inference(resolution,[status(thm)],[c_20,c_34]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_19,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | v1_relat_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_704,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ v1_partfun1(X0,X1)
% 7.73/1.50      | k1_relat_1(X0) = X1 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_702,c_34,c_20,c_19]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_705,plain,
% 7.73/1.50      ( ~ v1_partfun1(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | k1_relat_1(X0) = X1 ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_704]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_742,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | v1_xboole_0(X2)
% 7.73/1.50      | k1_relat_1(X0) = X1 ),
% 7.73/1.50      inference(resolution,[status(thm)],[c_25,c_705]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_744,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | v1_xboole_0(X2)
% 7.73/1.50      | k1_relat_1(X0) = X1 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_742,c_34,c_25,c_20,c_19]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_745,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | v1_xboole_0(X2)
% 7.73/1.50      | k1_relat_1(X0) = X1 ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_744]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2938,plain,
% 7.73/1.50      ( k1_relat_1(X0) = X1
% 7.73/1.50      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_xboole_0(X2) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3575,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top
% 7.73/1.50      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2949,c_2938]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_47,negated_conjecture,
% 7.73/1.50      ( v1_funct_1(sK6) ),
% 7.73/1.50      inference(cnf_transformation,[],[f128]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_62,plain,
% 7.73/1.50      ( v1_funct_1(sK6) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_46,negated_conjecture,
% 7.73/1.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f129]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_63,plain,
% 7.73/1.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3750,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_3575,c_62,c_63]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10,plain,
% 7.73/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2971,plain,
% 7.73/1.50      ( v1_xboole_0(X0) != iProver_top
% 7.73/1.50      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_15,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_8,plain,
% 7.73/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_652,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_xboole_0(X0,X1) = X0 ),
% 7.73/1.50      inference(resolution,[status(thm)],[c_15,c_8]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2939,plain,
% 7.73/1.50      ( k3_xboole_0(X0,X1) = X0
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3816,plain,
% 7.73/1.50      ( k3_xboole_0(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = sK6 ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2949,c_2939]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_6,plain,
% 7.73/1.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f135]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2974,plain,
% 7.73/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.73/1.50      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4464,plain,
% 7.73/1.50      ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top
% 7.73/1.50      | r2_hidden(X0,sK6) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3816,c_2974]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1,plain,
% 7.73/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2979,plain,
% 7.73/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.73/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4641,plain,
% 7.73/1.50      ( r2_hidden(X0,sK6) != iProver_top
% 7.73/1.50      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_4464,c_2979]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4742,plain,
% 7.73/1.50      ( r2_hidden(X0,sK6) != iProver_top
% 7.73/1.50      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2971,c_4641]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4849,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | r2_hidden(X0,sK6) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3750,c_4742]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11037,plain,
% 7.73/1.50      ( k3_xboole_0(sK6,X0) = k1_xboole_0
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_4434,c_4849]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14,plain,
% 7.73/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_139,plain,
% 7.73/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_138,plain,
% 7.73/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_140,plain,
% 7.73/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_138]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_29,plain,
% 7.73/1.50      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.73/1.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f142]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2962,plain,
% 7.73/1.50      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.73/1.50      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.73/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12,plain,
% 7.73/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f138]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2988,plain,
% 7.73/1.50      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.73/1.50      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.73/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_2962,c_12]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2995,plain,
% 7.73/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.73/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 7.73/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_2988]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2994,plain,
% 7.73/1.50      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 7.73/1.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.73/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2988]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2996,plain,
% 7.73/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.73/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 7.73/1.50      | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_2994]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1972,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | v1_funct_2(X3,X4,X5)
% 7.73/1.50      | X3 != X0
% 7.73/1.50      | X4 != X1
% 7.73/1.50      | X5 != X2 ),
% 7.73/1.50      theory(equality) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4921,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X2
% 7.73/1.50      | u1_struct_0(sK3) != X1
% 7.73/1.50      | sK6 != X0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1972]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4923,plain,
% 7.73/1.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 7.73/1.50      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0
% 7.73/1.50      | u1_struct_0(sK3) != k1_xboole_0
% 7.73/1.50      | sK6 != k1_xboole_0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_4921]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2970,plain,
% 7.73/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_21,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2968,plain,
% 7.73/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4944,plain,
% 7.73/1.50      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2970,c_2968]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_18,plain,
% 7.73/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4949,plain,
% 7.73/1.50      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_4944,c_18]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4954,plain,
% 7.73/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_4949]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4077,plain,
% 7.73/1.50      ( v1_xboole_0(X0) != iProver_top
% 7.73/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_12,c_2971]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4305,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3750,c_4077]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9,plain,
% 7.73/1.50      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2972,plain,
% 7.73/1.50      ( X0 = X1
% 7.73/1.50      | v1_xboole_0(X1) != iProver_top
% 7.73/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4935,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3750,c_2972]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5267,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_4305,c_4935]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4356,plain,
% 7.73/1.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2965,c_2979]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_7789,plain,
% 7.73/1.50      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 7.73/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2971,c_4356]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9017,plain,
% 7.73/1.50      ( k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = k1_xboole_0
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3750,c_7789]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_39,plain,
% 7.73/1.50      ( ~ v5_pre_topc(X0,X1,X2)
% 7.73/1.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.73/1.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.73/1.50      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v1_funct_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f146]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2954,plain,
% 7.73/1.50      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.73/1.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X2) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X2) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5497,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 7.73/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2949,c_2954]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_54,negated_conjecture,
% 7.73/1.50      ( v2_pre_topc(sK3) ),
% 7.73/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_55,plain,
% 7.73/1.50      ( v2_pre_topc(sK3) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_53,negated_conjecture,
% 7.73/1.50      ( l1_pre_topc(sK3) ),
% 7.73/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_56,plain,
% 7.73/1.50      ( l1_pre_topc(sK3) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_52,negated_conjecture,
% 7.73/1.50      ( v2_pre_topc(sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_57,plain,
% 7.73/1.50      ( v2_pre_topc(sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_51,negated_conjecture,
% 7.73/1.50      ( l1_pre_topc(sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f124]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_58,plain,
% 7.73/1.50      ( l1_pre_topc(sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_64,plain,
% 7.73/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_42,negated_conjecture,
% 7.73/1.50      ( ~ v5_pre_topc(sK5,sK3,sK4)
% 7.73/1.50      | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f133]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2951,plain,
% 7.73/1.50      ( v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_44,negated_conjecture,
% 7.73/1.50      ( sK5 = sK6 ),
% 7.73/1.50      inference(cnf_transformation,[],[f131]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2986,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_2951,c_44]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_49,negated_conjecture,
% 7.73/1.50      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f126]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2945,plain,
% 7.73/1.50      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2982,plain,
% 7.73/1.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_2945,c_44]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_43,negated_conjecture,
% 7.73/1.50      ( v5_pre_topc(sK5,sK3,sK4)
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f132]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2950,plain,
% 7.73/1.50      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2985,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_2950,c_44]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_48,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f127]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2946,plain,
% 7.73/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2983,plain,
% 7.73/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_2946,c_44]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_37,plain,
% 7.73/1.50      ( ~ v2_pre_topc(X0)
% 7.73/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.73/1.50      | ~ l1_pre_topc(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3141,plain,
% 7.73/1.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 7.73/1.50      | ~ v2_pre_topc(sK4)
% 7.73/1.50      | ~ l1_pre_topc(sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_37]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3142,plain,
% 7.73/1.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3141]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_35,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3373,plain,
% 7.73/1.50      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_35]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3374,plain,
% 7.73/1.50      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3373]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_36,plain,
% 7.73/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.73/1.50      | ~ l1_pre_topc(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f115]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3565,plain,
% 7.73/1.50      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 7.73/1.50      | ~ l1_pre_topc(sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_36]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3566,plain,
% 7.73/1.50      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3565]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_40,plain,
% 7.73/1.50      ( v5_pre_topc(X0,X1,X2)
% 7.73/1.50      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.73/1.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.73/1.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v1_funct_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f147]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3300,plain,
% 7.73/1.50      ( ~ v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 7.73/1.50      | v5_pre_topc(sK6,X0,sK4)
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 7.73/1.50      | ~ v2_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(sK4)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ l1_pre_topc(sK4)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_40]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3878,plain,
% 7.73/1.50      ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 7.73/1.50      | v5_pre_topc(sK6,sK3,sK4)
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 7.73/1.50      | ~ v2_pre_topc(sK4)
% 7.73/1.50      | ~ v2_pre_topc(sK3)
% 7.73/1.50      | ~ l1_pre_topc(sK4)
% 7.73/1.50      | ~ l1_pre_topc(sK3)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_3300]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3879,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3878]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_38,plain,
% 7.73/1.50      ( v5_pre_topc(X0,X1,X2)
% 7.73/1.50      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.73/1.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.73/1.50      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v1_funct_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f145]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3517,plain,
% 7.73/1.50      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
% 7.73/1.50      | v5_pre_topc(sK6,sK3,X0)
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X0))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 7.73/1.50      | ~ v2_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(sK3)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ l1_pre_topc(sK3)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_38]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3913,plain,
% 7.73/1.50      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 7.73/1.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 7.73/1.50      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 7.73/1.50      | ~ v2_pre_topc(sK3)
% 7.73/1.50      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 7.73/1.50      | ~ l1_pre_topc(sK3)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_3517]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3914,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 7.73/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3913]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_41,plain,
% 7.73/1.50      ( ~ v5_pre_topc(X0,X1,X2)
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.73/1.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.73/1.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v1_funct_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f148]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3829,plain,
% 7.73/1.50      ( ~ v5_pre_topc(sK6,sK3,X0)
% 7.73/1.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X0))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 7.73/1.50      | ~ v2_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(sK3)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ l1_pre_topc(sK3)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_41]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5291,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 7.73/1.50      | ~ v5_pre_topc(sK6,sK3,sK4)
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 7.73/1.50      | ~ v2_pre_topc(sK4)
% 7.73/1.50      | ~ v2_pre_topc(sK3)
% 7.73/1.50      | ~ l1_pre_topc(sK4)
% 7.73/1.50      | ~ l1_pre_topc(sK3)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_3829]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5292,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,sK4) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_5291]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5675,plain,
% 7.73/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5497,c_55,c_56,c_57,c_58,c_62,c_63,c_64,c_2986,c_2982,
% 7.73/1.50                 c_2985,c_2983,c_3142,c_3374,c_3566,c_3879,c_3914,c_5292]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5676,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_5675]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5679,plain,
% 7.73/1.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5676,c_55,c_56,c_57,c_58,c_62,c_63,c_64,c_2982,c_2985,
% 7.73/1.50                 c_2983,c_3142,c_3374,c_3566,c_3914,c_5292]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9795,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_9017,c_5679]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9794,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_9017,c_2949]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10392,plain,
% 7.73/1.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_9795,c_9794]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10393,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_10392]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10394,plain,
% 7.73/1.50      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_10393]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3817,plain,
% 7.73/1.50      ( k3_xboole_0(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = sK6 ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2983,c_2939]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11027,plain,
% 7.73/1.50      ( k3_xboole_0(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = k1_xboole_0
% 7.73/1.50      | r2_hidden(sK2(sK6),sK6) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3817,c_4434]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11043,plain,
% 7.73/1.50      ( sK6 = k1_xboole_0 | r2_hidden(sK2(sK6),sK6) = iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11027,c_3817]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4861,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | sK6 = k1_xboole_0 ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2965,c_4849]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2948,plain,
% 7.73/1.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9966,plain,
% 7.73/1.50      ( sK6 = k1_xboole_0
% 7.73/1.50      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_4861,c_2948]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3384,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top
% 7.73/1.50      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2983,c_2938]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3633,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_3384,c_62,c_2982]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4934,plain,
% 7.73/1.50      ( u1_struct_0(sK4) = X0
% 7.73/1.50      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3633,c_2972]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5261,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4)
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3750,c_4934]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5338,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5261,c_2948]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2952,plain,
% 7.73/1.50      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X2) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X2) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4427,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2949,c_2952]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3126,plain,
% 7.73/1.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.73/1.50      | ~ v2_pre_topc(sK3)
% 7.73/1.50      | ~ l1_pre_topc(sK3) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_37]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3127,plain,
% 7.73/1.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3126]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3363,plain,
% 7.73/1.50      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_35]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3364,plain,
% 7.73/1.50      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3363]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3542,plain,
% 7.73/1.50      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 7.73/1.50      | ~ l1_pre_topc(sK3) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_36]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3543,plain,
% 7.73/1.50      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3542]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3904,plain,
% 7.73/1.50      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 7.73/1.50      | v5_pre_topc(sK6,sK3,sK4)
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 7.73/1.50      | ~ v2_pre_topc(sK4)
% 7.73/1.50      | ~ v2_pre_topc(sK3)
% 7.73/1.50      | ~ l1_pre_topc(sK4)
% 7.73/1.50      | ~ l1_pre_topc(sK3)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_3517]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3905,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3904]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4565,plain,
% 7.73/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_4427,c_55,c_56,c_57,c_58,c_62,c_63,c_2986,c_2982,
% 7.73/1.50                 c_2983,c_3127,c_3364,c_3543,c_3905]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4566,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_4565]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2953,plain,
% 7.73/1.50      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X2) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X2) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4865,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2949,c_2953]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5169,plain,
% 7.73/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_4865,c_55,c_56,c_57,c_58,c_62,c_63,c_2986,c_2982,
% 7.73/1.50                 c_2983,c_3127,c_3364,c_3543,c_3905,c_4427]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5170,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_5169]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5173,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2985,c_5170]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3802,plain,
% 7.73/1.50      ( ~ v5_pre_topc(sK6,X0,sK4)
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
% 7.73/1.50      | ~ v2_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(sK4)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ l1_pre_topc(sK4)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_39]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5277,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 7.73/1.50      | ~ v5_pre_topc(sK6,sK3,sK4)
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 7.73/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 7.73/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 7.73/1.50      | ~ v2_pre_topc(sK4)
% 7.73/1.50      | ~ v2_pre_topc(sK3)
% 7.73/1.50      | ~ l1_pre_topc(sK4)
% 7.73/1.50      | ~ l1_pre_topc(sK3)
% 7.73/1.50      | ~ v1_funct_1(sK6) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_3802]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5278,plain,
% 7.73/1.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
% 7.73/1.50      | v5_pre_topc(sK6,sK3,sK4) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_5277]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5337,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5261,c_2949]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5361,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5338,c_55,c_56,c_57,c_58,c_62,c_2982,c_2983,c_4566,
% 7.73/1.50                 c_5173,c_5278,c_5337]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5362,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 7.73/1.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_5361]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5372,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | r2_hidden(X0,sK6) != iProver_top
% 7.73/1.50      | v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5362,c_4641]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4465,plain,
% 7.73/1.50      ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top
% 7.73/1.50      | r2_hidden(X0,sK6) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3817,c_2974]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4636,plain,
% 7.73/1.50      ( r2_hidden(X0,sK6) != iProver_top
% 7.73/1.50      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_4465,c_2979]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4737,plain,
% 7.73/1.50      ( r2_hidden(X0,sK6) != iProver_top
% 7.73/1.50      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2971,c_4636]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5858,plain,
% 7.73/1.50      ( r2_hidden(X0,sK6) != iProver_top
% 7.73/1.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5372,c_3633,c_4737]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5859,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | r2_hidden(X0,sK6) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_5858]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5865,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6) | sK6 = k1_xboole_0 ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2965,c_5859]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9965,plain,
% 7.73/1.50      ( sK6 = k1_xboole_0
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_4861,c_2949]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_7838,plain,
% 7.73/1.50      ( sK6 = k1_xboole_0
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5865,c_5679]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10314,plain,
% 7.73/1.50      ( sK6 = k1_xboole_0
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_9965,c_7838]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10319,plain,
% 7.73/1.50      ( sK6 = k1_xboole_0
% 7.73/1.50      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5865,c_10314]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11597,plain,
% 7.73/1.50      ( sK6 = k1_xboole_0 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_11043,c_9966,c_10319]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11664,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 7.73/1.50      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11597,c_3633]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11673,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_11664,c_18]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12114,plain,
% 7.73/1.50      ( u1_struct_0(sK4) = k1_xboole_0 | u1_struct_0(sK3) = k1_xboole_0 ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_11673,c_4356]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_7841,plain,
% 7.73/1.50      ( sK6 = k1_xboole_0
% 7.73/1.50      | v5_pre_topc(sK6,g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5865,c_5170]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_8411,plain,
% 7.73/1.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_7841,c_55,c_56,c_57,c_58,c_62,c_63,c_2986,c_2982,
% 7.73/1.50                 c_2983,c_3127,c_3364,c_3543,c_3905,c_4427,c_5173,c_5278]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_8415,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5362,c_8411]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_8605,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5362,c_8415]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11618,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 7.73/1.50      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11597,c_8605]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11723,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4)))) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_11618,c_18]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11724,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11723,c_12]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_13325,plain,
% 7.73/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top
% 7.73/1.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_11724,c_140]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_13326,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_13325]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17930,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_12114,c_13326]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_19844,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_11037,c_139,c_140,c_2995,c_2996,c_4923,c_4954,c_5267,
% 7.73/1.50                 c_9966,c_10319,c_10394,c_17930]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5369,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(sK6)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5362,c_2952]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_6776,plain,
% 7.73/1.50      ( l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(sK6)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5369,c_55,c_56]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_6777,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(sK6)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_6776]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_6783,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),k1_relat_1(sK6)) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(sK6)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5362,c_6777]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11633,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),k1_relat_1(k1_xboole_0)) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_relat_1(k1_xboole_0)))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11597,c_6783]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11699,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_11633,c_18]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11,plain,
% 7.73/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f137]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11700,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11699,c_11]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17907,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v5_pre_topc(X0,sK4,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,sK4,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(sK4),k1_xboole_0) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_12114,c_11700]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17949,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0
% 7.73/1.50      | v5_pre_topc(X0,sK4,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.73/1.50      | v5_pre_topc(X0,sK4,sK3) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.73/1.50      | v1_funct_2(X0,u1_struct_0(sK4),k1_xboole_0) != iProver_top
% 7.73/1.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK4) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK4) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_17907,c_12]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_18163,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = k1_xboole_0 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_17949,c_140,c_2995,c_4954,c_17930]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_19846,plain,
% 7.73/1.50      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))) = k1_xboole_0 ),
% 7.73/1.50      inference(light_normalisation,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_19844,c_18,c_11597,c_18163]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11668,plain,
% 7.73/1.50      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11597,c_2948]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_18188,plain,
% 7.73/1.50      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_18163,c_11668]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_19849,plain,
% 7.73/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_19846,c_18188]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11646,plain,
% 7.73/1.50      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.73/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11597,c_5679]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12492,plain,
% 7.73/1.50      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2970,c_11646]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_18175,plain,
% 7.73/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_18163,c_12492]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(contradiction,plain,
% 7.73/1.50      ( $false ),
% 7.73/1.50      inference(minisat,[status(thm)],[c_19849,c_18175]) ).
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  ------                               Statistics
% 7.73/1.50  
% 7.73/1.50  ------ General
% 7.73/1.50  
% 7.73/1.50  abstr_ref_over_cycles:                  0
% 7.73/1.50  abstr_ref_under_cycles:                 0
% 7.73/1.50  gc_basic_clause_elim:                   0
% 7.73/1.50  forced_gc_time:                         0
% 7.73/1.50  parsing_time:                           0.014
% 7.73/1.50  unif_index_cands_time:                  0.
% 7.73/1.50  unif_index_add_time:                    0.
% 7.73/1.50  orderings_time:                         0.
% 7.73/1.50  out_proof_time:                         0.024
% 7.73/1.50  total_time:                             0.651
% 7.73/1.50  num_of_symbols:                         61
% 7.73/1.50  num_of_terms:                           18754
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing
% 7.73/1.50  
% 7.73/1.50  num_of_splits:                          0
% 7.73/1.50  num_of_split_atoms:                     0
% 7.73/1.50  num_of_reused_defs:                     0
% 7.73/1.50  num_eq_ax_congr_red:                    41
% 7.73/1.50  num_of_sem_filtered_clauses:            1
% 7.73/1.50  num_of_subtypes:                        0
% 7.73/1.50  monotx_restored_types:                  0
% 7.73/1.50  sat_num_of_epr_types:                   0
% 7.73/1.50  sat_num_of_non_cyclic_types:            0
% 7.73/1.50  sat_guarded_non_collapsed_types:        0
% 7.73/1.50  num_pure_diseq_elim:                    0
% 7.73/1.50  simp_replaced_by:                       0
% 7.73/1.50  res_preprocessed:                       238
% 7.73/1.50  prep_upred:                             0
% 7.73/1.50  prep_unflattend:                        24
% 7.73/1.50  smt_new_axioms:                         0
% 7.73/1.50  pred_elim_cands:                        8
% 7.73/1.50  pred_elim:                              4
% 7.73/1.50  pred_elim_cl:                           5
% 7.73/1.50  pred_elim_cycles:                       7
% 7.73/1.50  merged_defs:                            8
% 7.73/1.50  merged_defs_ncl:                        0
% 7.73/1.50  bin_hyper_res:                          8
% 7.73/1.50  prep_cycles:                            4
% 7.73/1.50  pred_elim_time:                         0.021
% 7.73/1.50  splitting_time:                         0.
% 7.73/1.50  sem_filter_time:                        0.
% 7.73/1.50  monotx_time:                            0.001
% 7.73/1.50  subtype_inf_time:                       0.
% 7.73/1.50  
% 7.73/1.50  ------ Problem properties
% 7.73/1.50  
% 7.73/1.50  clauses:                                49
% 7.73/1.50  conjectures:                            13
% 7.73/1.50  epr:                                    9
% 7.73/1.50  horn:                                   38
% 7.73/1.50  ground:                                 15
% 7.73/1.50  unary:                                  16
% 7.73/1.50  binary:                                 12
% 7.73/1.50  lits:                                   141
% 7.73/1.50  lits_eq:                                29
% 7.73/1.50  fd_pure:                                0
% 7.73/1.50  fd_pseudo:                              0
% 7.73/1.50  fd_cond:                                7
% 7.73/1.50  fd_pseudo_cond:                         5
% 7.73/1.50  ac_symbols:                             0
% 7.73/1.50  
% 7.73/1.50  ------ Propositional Solver
% 7.73/1.50  
% 7.73/1.50  prop_solver_calls:                      34
% 7.73/1.50  prop_fast_solver_calls:                 3410
% 7.73/1.50  smt_solver_calls:                       0
% 7.73/1.50  smt_fast_solver_calls:                  0
% 7.73/1.50  prop_num_of_clauses:                    8465
% 7.73/1.50  prop_preprocess_simplified:             17820
% 7.73/1.50  prop_fo_subsumed:                       164
% 7.73/1.50  prop_solver_time:                       0.
% 7.73/1.50  smt_solver_time:                        0.
% 7.73/1.50  smt_fast_solver_time:                   0.
% 7.73/1.50  prop_fast_solver_time:                  0.
% 7.73/1.50  prop_unsat_core_time:                   0.
% 7.73/1.50  
% 7.73/1.50  ------ QBF
% 7.73/1.50  
% 7.73/1.50  qbf_q_res:                              0
% 7.73/1.50  qbf_num_tautologies:                    0
% 7.73/1.50  qbf_prep_cycles:                        0
% 7.73/1.50  
% 7.73/1.50  ------ BMC1
% 7.73/1.50  
% 7.73/1.50  bmc1_current_bound:                     -1
% 7.73/1.50  bmc1_last_solved_bound:                 -1
% 7.73/1.50  bmc1_unsat_core_size:                   -1
% 7.73/1.50  bmc1_unsat_core_parents_size:           -1
% 7.73/1.50  bmc1_merge_next_fun:                    0
% 7.73/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.50  
% 7.73/1.50  ------ Instantiation
% 7.73/1.50  
% 7.73/1.50  inst_num_of_clauses:                    2022
% 7.73/1.50  inst_num_in_passive:                    1060
% 7.73/1.50  inst_num_in_active:                     941
% 7.73/1.50  inst_num_in_unprocessed:                21
% 7.73/1.50  inst_num_of_loops:                      1300
% 7.73/1.50  inst_num_of_learning_restarts:          0
% 7.73/1.50  inst_num_moves_active_passive:          354
% 7.73/1.50  inst_lit_activity:                      0
% 7.73/1.50  inst_lit_activity_moves:                0
% 7.73/1.50  inst_num_tautologies:                   0
% 7.73/1.50  inst_num_prop_implied:                  0
% 7.73/1.50  inst_num_existing_simplified:           0
% 7.73/1.50  inst_num_eq_res_simplified:             0
% 7.73/1.50  inst_num_child_elim:                    0
% 7.73/1.50  inst_num_of_dismatching_blockings:      932
% 7.73/1.50  inst_num_of_non_proper_insts:           2326
% 7.73/1.50  inst_num_of_duplicates:                 0
% 7.73/1.50  inst_inst_num_from_inst_to_res:         0
% 7.73/1.50  inst_dismatching_checking_time:         0.
% 7.73/1.50  
% 7.73/1.50  ------ Resolution
% 7.73/1.50  
% 7.73/1.50  res_num_of_clauses:                     0
% 7.73/1.50  res_num_in_passive:                     0
% 7.73/1.50  res_num_in_active:                      0
% 7.73/1.50  res_num_of_loops:                       242
% 7.73/1.50  res_forward_subset_subsumed:            64
% 7.73/1.50  res_backward_subset_subsumed:           0
% 7.73/1.50  res_forward_subsumed:                   0
% 7.73/1.50  res_backward_subsumed:                  0
% 7.73/1.50  res_forward_subsumption_resolution:     1
% 7.73/1.50  res_backward_subsumption_resolution:    0
% 7.73/1.50  res_clause_to_clause_subsumption:       1811
% 7.73/1.50  res_orphan_elimination:                 0
% 7.73/1.50  res_tautology_del:                      120
% 7.73/1.50  res_num_eq_res_simplified:              0
% 7.73/1.50  res_num_sel_changes:                    0
% 7.73/1.50  res_moves_from_active_to_pass:          0
% 7.73/1.50  
% 7.73/1.50  ------ Superposition
% 7.73/1.50  
% 7.73/1.50  sup_time_total:                         0.
% 7.73/1.50  sup_time_generating:                    0.
% 7.73/1.50  sup_time_sim_full:                      0.
% 7.73/1.50  sup_time_sim_immed:                     0.
% 7.73/1.50  
% 7.73/1.50  sup_num_of_clauses:                     313
% 7.73/1.50  sup_num_in_active:                      89
% 7.73/1.50  sup_num_in_passive:                     224
% 7.73/1.50  sup_num_of_loops:                       258
% 7.73/1.50  sup_fw_superposition:                   424
% 7.73/1.50  sup_bw_superposition:                   547
% 7.73/1.50  sup_immediate_simplified:               355
% 7.73/1.50  sup_given_eliminated:                   5
% 7.73/1.50  comparisons_done:                       0
% 7.73/1.50  comparisons_avoided:                    51
% 7.73/1.50  
% 7.73/1.50  ------ Simplifications
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  sim_fw_subset_subsumed:                 149
% 7.73/1.50  sim_bw_subset_subsumed:                 210
% 7.73/1.50  sim_fw_subsumed:                        87
% 7.73/1.50  sim_bw_subsumed:                        30
% 7.73/1.50  sim_fw_subsumption_res:                 0
% 7.73/1.50  sim_bw_subsumption_res:                 0
% 7.73/1.50  sim_tautology_del:                      58
% 7.73/1.50  sim_eq_tautology_del:                   51
% 7.73/1.50  sim_eq_res_simp:                        3
% 7.73/1.50  sim_fw_demodulated:                     119
% 7.73/1.50  sim_bw_demodulated:                     104
% 7.73/1.50  sim_light_normalised:                   118
% 7.73/1.50  sim_joinable_taut:                      0
% 7.73/1.50  sim_joinable_simp:                      0
% 7.73/1.50  sim_ac_normalised:                      0
% 7.73/1.50  sim_smt_subsumption:                    0
% 7.73/1.50  
%------------------------------------------------------------------------------
