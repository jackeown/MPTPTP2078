%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2057+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:06 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  158 (1869 expanded)
%              Number of clauses        :  101 ( 397 expanded)
%              Number of leaves         :   15 ( 515 expanded)
%              Depth                    :   30
%              Number of atoms          :  736 (17824 expanded)
%              Number of equality atoms :  128 ( 345 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f24])).

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
    inference(flattening,[],[f29])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).

fof(f52,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(pure_predicate_removal,[],[f3])).

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

fof(f53,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f45,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19,negated_conjecture,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

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

cnf(c_18,negated_conjecture,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_349,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_350,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_354,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_20])).

cnf(c_355,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_440,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_355])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_609,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_440,c_21])).

cnf(c_610,plain,
    ( l1_waybel_0(k3_yellow19(sK0,X0,sK1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_614,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_waybel_0(k3_yellow19(sK0,X0,sK1),sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_22])).

cnf(c_615,plain,
    ( l1_waybel_0(k3_yellow19(sK0,X0,sK1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_614])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_636,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_637,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_58,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_639,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_22,c_21,c_58])).

cnf(c_919,plain,
    ( l1_waybel_0(k3_yellow19(sK0,X0,sK1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | k2_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_615,c_639])).

cnf(c_920,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_68,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_922,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_920,c_21,c_17,c_68])).

cnf(c_6,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_169,plain,
    ( r2_hidden(sK2,sK1)
    | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_170,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_568,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_170])).

cnf(c_569,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_571,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_22,c_21,c_15])).

cnf(c_572,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_571])).

cnf(c_972,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_922,c_572])).

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

cnf(c_313,plain,
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
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_314,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_318,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_20])).

cnf(c_319,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_319])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_469,c_21])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_659,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_655,c_22])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_659])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | k2_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_660,c_639])).

cnf(c_906,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_908,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_906,c_21,c_17,c_68])).

cnf(c_974,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_972,c_908])).

cnf(c_975,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_974])).

cnf(c_2188,plain,
    ( k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_975])).

cnf(c_2254,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2188])).

cnf(c_3,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_933,plain,
    ( sK2 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_1823,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_975])).

cnf(c_1824,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1823])).

cnf(c_1726,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2404,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_1727,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2387,plain,
    ( sK2 != X0
    | sK2 = o_0_0_xboole_0
    | o_0_0_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_2475,plain,
    ( sK2 != sK2
    | sK2 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2459,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(o_0_0_xboole_0)))
    | o_0_0_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2689,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
    | ~ r2_hidden(sK2,sK1)
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2459])).

cnf(c_2699,plain,
    ( o_0_0_xboole_0 = sK2
    | r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) = iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2689])).

cnf(c_8,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,negated_conjecture,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_167,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_168,plain,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_548,plain,
    ( ~ r2_hidden(X0,k2_yellow19(X1,X2))
    | ~ r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X2
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_168])).

cnf(c_549,plain,
    ( ~ r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_551,plain,
    ( ~ r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,sK1)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_22,c_21])).

cnf(c_988,plain,
    ( ~ r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,sK1)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_922,c_551])).

cnf(c_990,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_908])).

cnf(c_991,plain,
    ( ~ r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,sK1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_990])).

cnf(c_2187,plain,
    ( k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_2265,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2187])).

cnf(c_2194,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2199,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2575,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2194,c_2199])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_385,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | k3_yellow_1(k2_struct_0(X1)) != k3_yellow_1(k2_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_386,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_20])).

cnf(c_391,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_498,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_391])).

cnf(c_598,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_498,c_21])).

cnf(c_599,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_601,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_22,c_17])).

cnf(c_2251,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_601])).

cnf(c_2679,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_2575,c_2251])).

cnf(c_3093,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) != iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2265,c_2679])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2196,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3096,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3093,c_2196])).

cnf(c_3279,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2254,c_933,c_1824,c_2404,c_2475,c_2699,c_3096])).

cnf(c_3283,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3279,c_2679])).

cnf(c_3285,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3283,c_3096])).


%------------------------------------------------------------------------------
