%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2057+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:06 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  163 (1893 expanded)
%              Number of clauses        :  106 ( 415 expanded)
%              Number of leaves         :   15 ( 518 expanded)
%              Depth                    :   28
%              Number of atoms          :  731 (17827 expanded)
%              Number of equality atoms :  139 ( 373 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
             => ( r2_hidden(X2,X1)
              <=> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X2,X1)
                <=> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,X1)
              <~> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,X1)
              <~> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | ~ r2_hidden(X2,X1) )
              & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | r2_hidden(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | ~ r2_hidden(X2,X1) )
              & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | r2_hidden(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
            | ~ r2_hidden(X2,X1) )
          & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
            | r2_hidden(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X2) )
     => ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)
          | ~ r2_hidden(sK2,X1) )
        & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)
          | r2_hidden(sK2,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | ~ r2_hidden(X2,X1) )
              & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | r2_hidden(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)
              | ~ r2_hidden(X2,sK1) )
            & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)
              | r2_hidden(X2,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X2) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                  | ~ r2_hidden(X2,X1) )
                & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                  | r2_hidden(X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)
                | ~ r2_hidden(X2,X1) )
              & ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)
                | r2_hidden(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
      | ~ r2_hidden(sK2,sK1) )
    & ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
      | r2_hidden(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f58,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_178,plain,
    ( r2_hidden(sK2,sK1)
    | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_179,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_582,plain,
    ( r2_hidden(X0,k2_yellow19(X1,X2))
    | r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X2
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_179])).

cnf(c_583,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_585,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_23,c_22,c_16])).

cnf(c_586,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_585])).

cnf(c_2476,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_20,negated_conjecture,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,negated_conjecture,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_327,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_328,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_332,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_21])).

cnf(c_333,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_333])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_483,c_22])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_673,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_23])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_673])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_650,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_651,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_62,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_653,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_23,c_22,c_62])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | k2_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_674,c_653])).

cnf(c_1127,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1126])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_0,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_72,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1129,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1127,c_22,c_18,c_72])).

cnf(c_2467,plain,
    ( k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_2514,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2467])).

cnf(c_1,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_363,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_364,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_368,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_21])).

cnf(c_369,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_368])).

cnf(c_454,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_369])).

cnf(c_623,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_454,c_22])).

cnf(c_624,plain,
    ( l1_waybel_0(k3_yellow19(sK0,X0,sK1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_628,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_waybel_0(k3_yellow19(sK0,X0,sK1),sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_23])).

cnf(c_629,plain,
    ( l1_waybel_0(k3_yellow19(sK0,X0,sK1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_628])).

cnf(c_1140,plain,
    ( l1_waybel_0(k3_yellow19(sK0,X0,sK1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | k2_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_629,c_653])).

cnf(c_1141,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1140])).

cnf(c_1143,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_22,c_18,c_72])).

cnf(c_2466,plain,
    ( k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_2511,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2466])).

cnf(c_2567,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2476,c_2514,c_2511])).

cnf(c_587,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_3,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1154,plain,
    ( sK2 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_2032,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_1143])).

cnf(c_2033,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2032])).

cnf(c_2034,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1129])).

cnf(c_2035,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_1956,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2740,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_1957,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2715,plain,
    ( sK2 != X0
    | sK2 = o_0_0_xboole_0
    | o_0_0_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_2837,plain,
    ( sK2 != sK2
    | sK2 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2715])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2800,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(o_0_0_xboole_0)))
    | o_0_0_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3133,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
    | ~ r2_hidden(sK2,sK1)
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2800])).

cnf(c_3143,plain,
    ( o_0_0_xboole_0 = sK2
    | r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) = iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3133])).

cnf(c_8,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_176,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_177,plain,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_562,plain,
    ( ~ r2_hidden(X0,k2_yellow19(X1,X2))
    | ~ r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X2
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_177])).

cnf(c_563,plain,
    ( ~ r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_565,plain,
    ( ~ r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_23,c_22])).

cnf(c_2477,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | r2_hidden(sK2,sK1) != iProver_top
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_2596,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2477,c_2514,c_2511])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_399,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | k3_yellow_1(k2_struct_0(X1)) != k3_yellow_1(k2_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_400,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_404,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_21])).

cnf(c_405,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_404])).

cnf(c_512,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_405])).

cnf(c_612,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_512,c_22])).

cnf(c_613,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_615,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_23,c_18])).

cnf(c_2523,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_615])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1055,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_3])).

cnf(c_1056,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1055])).

cnf(c_2524,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_2523,c_1056])).

cnf(c_2479,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2484,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2878,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2479,c_2484])).

cnf(c_3090,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_2524,c_2878])).

cnf(c_3630,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) != iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2596,c_3090])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2481,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3633,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3630,c_2481])).

cnf(c_3638,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2567,c_587,c_1154,c_2033,c_2035,c_2740,c_2837,c_3143,c_3633])).

cnf(c_3642,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3638,c_3090])).

cnf(c_3644,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3642,c_3633])).


%------------------------------------------------------------------------------
