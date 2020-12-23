%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:17 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  225 (1914 expanded)
%              Number of clauses        :  145 ( 403 expanded)
%              Number of leaves         :   16 ( 531 expanded)
%              Depth                    :   37
%              Number of atoms          : 1403 (16846 expanded)
%              Number of equality atoms :  167 ( 407 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_7(X0,X1,X2)
            | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & ( r1_waybel_7(X0,X1,X2)
            | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_waybel_7(X0,X1,sK3)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3) )
        & ( r1_waybel_7(X0,X1,sK3)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r1_waybel_7(X0,sK2,X2)
              | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2) )
            & ( r1_waybel_7(X0,sK2,X2)
              | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_7(X0,X1,X2)
                  | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & ( r1_waybel_7(X0,X1,X2)
                  | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(sK1,X1,X2)
                | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2) )
              & ( r1_waybel_7(sK1,X1,X2)
                | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r1_waybel_7(sK1,sK2,sK3)
      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) )
    & ( r1_waybel_7(sK1,sK2,sK3)
      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    & ~ v1_xboole_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f45,f44,f43])).

fof(f70,plain,(
    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f70,f55])).

fof(f7,axiom,(
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

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f55,f55,f55])).

fof(f75,plain,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f71,f55])).

fof(f68,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(definition_unfolding,[],[f72,f55])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f55,f55,f55])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f55,f55,f55])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f55,f55,f55,f55])).

fof(f69,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(definition_unfolding,[],[f69,f55])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f55,f55,f55,f55])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3762,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X0_55)
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4132,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X0_55) = iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3762])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3763,plain,
    ( ~ r2_hidden(sK0(X0_55,X1_55),X1_55)
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4131,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X1_55) != iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3763])).

cnf(c_4438,plain,
    ( r1_tarski(X0_55,X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_4131])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3760,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4134,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) = iProver_top
    | r1_tarski(X0_55,X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3760])).

cnf(c_22,negated_conjecture,
    ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_8,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,negated_conjecture,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_212,plain,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_577,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_578,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_582,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_27,c_25])).

cnf(c_955,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_582])).

cnf(c_956,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_955])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_958,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_956,c_19])).

cnf(c_959,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_958])).

cnf(c_995,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_959])).

cnf(c_996,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_68,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1000,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_27,c_25,c_68])).

cnf(c_1001,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(renaming,[status(thm)],[c_1000])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1589,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1001,c_21])).

cnf(c_1590,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1589])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1594,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1590,c_24])).

cnf(c_1595,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1594])).

cnf(c_1938,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1595])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_626,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_627,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_1104,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_627])).

cnf(c_1105,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1104])).

cnf(c_65,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1107,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1105,c_27,c_25,c_65,c_68])).

cnf(c_2639,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | k2_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1938,c_1107])).

cnf(c_2640,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2639])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1153,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_627])).

cnf(c_1154,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1153])).

cnf(c_1158,plain,
    ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1154,c_27])).

cnf(c_1159,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1158])).

cnf(c_1484,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1159,c_21])).

cnf(c_1485,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1484])).

cnf(c_1489,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1485,c_24])).

cnf(c_1490,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1489])).

cnf(c_2037,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1490])).

cnf(c_2579,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | k2_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_2037,c_1107])).

cnf(c_2580,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2579])).

cnf(c_2582,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_20])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1120,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_627])).

cnf(c_1121,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1120])).

cnf(c_1125,plain,
    ( v4_orders_2(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1121,c_27])).

cnf(c_1126,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1125])).

cnf(c_1514,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1126,c_21])).

cnf(c_1515,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1514])).

cnf(c_1519,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1515,c_24])).

cnf(c_1520,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1519])).

cnf(c_2014,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1520])).

cnf(c_2596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | k2_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_2014,c_1107])).

cnf(c_2597,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2596])).

cnf(c_2599,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2597,c_20])).

cnf(c_2642,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2640,c_20,c_2582,c_2599])).

cnf(c_2643,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_2642])).

cnf(c_3307,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2643])).

cnf(c_12,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_23,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_454,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_455,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_459,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_24])).

cnf(c_460,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_459])).

cnf(c_1186,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_460,c_627])).

cnf(c_1187,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_1191,plain,
    ( v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1187,c_27])).

cnf(c_1192,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1191])).

cnf(c_1634,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1192])).

cnf(c_1912,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1634])).

cnf(c_2665,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k2_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1912,c_1107])).

cnf(c_2666,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_2665])).

cnf(c_2668,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2666,c_20])).

cnf(c_3305,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2668])).

cnf(c_3309,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3307,c_3305])).

cnf(c_3310,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_3309])).

cnf(c_3753,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_3310])).

cnf(c_4140,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) != iProver_top
    | r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3753])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_493,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_494,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_498,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_24])).

cnf(c_499,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_498])).

cnf(c_1093,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_499,c_627])).

cnf(c_1094,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v2_struct_0(sK1)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_1093])).

cnf(c_1096,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1094,c_27,c_22,c_21,c_20])).

cnf(c_3320,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1096])).

cnf(c_3751,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_3320])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1115,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_627])).

cnf(c_1116,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1115])).

cnf(c_3756,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1116])).

cnf(c_4178,plain,
    ( r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4140,c_3751,c_3756])).

cnf(c_18,negated_conjecture,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_214,plain,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_544,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_545,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_549,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_545,c_27,c_25])).

cnf(c_929,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_214,c_549])).

cnf(c_930,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_932,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | r1_waybel_7(sK1,sK2,sK3)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_19])).

cnf(c_933,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_932])).

cnf(c_1043,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_933])).

cnf(c_1044,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1043])).

cnf(c_1048,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1044,c_27,c_25,c_68])).

cnf(c_1049,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(renaming,[status(thm)],[c_1048])).

cnf(c_1544,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1049,c_21])).

cnf(c_1545,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1544])).

cnf(c_1549,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | r1_waybel_7(sK1,sK2,sK3)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1545,c_24])).

cnf(c_1550,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1549])).

cnf(c_1976,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1550])).

cnf(c_2613,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | k2_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1976,c_1107])).

cnf(c_2614,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2613])).

cnf(c_2616,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_waybel_7(sK1,sK2,sK3)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2614,c_20,c_2582,c_2599])).

cnf(c_2617,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_2616])).

cnf(c_3313,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2617])).

cnf(c_3315,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_waybel_7(sK1,sK2,sK3)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3313,c_3305])).

cnf(c_3316,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_3315])).

cnf(c_3752,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_3316])).

cnf(c_4141,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) = iProver_top
    | r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3752])).

cnf(c_4173,plain,
    ( r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4141,c_3751,c_3756])).

cnf(c_4181,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4178,c_4173])).

cnf(c_4331,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4134,c_4181])).

cnf(c_4475,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4438,c_4331])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:23:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.44/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.04  
% 1.44/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.44/1.04  
% 1.44/1.04  ------  iProver source info
% 1.44/1.04  
% 1.44/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.44/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.44/1.04  git: non_committed_changes: false
% 1.44/1.04  git: last_make_outside_of_git: false
% 1.44/1.04  
% 1.44/1.04  ------ 
% 1.44/1.04  
% 1.44/1.04  ------ Input Options
% 1.44/1.04  
% 1.44/1.04  --out_options                           all
% 1.44/1.04  --tptp_safe_out                         true
% 1.44/1.04  --problem_path                          ""
% 1.44/1.04  --include_path                          ""
% 1.44/1.04  --clausifier                            res/vclausify_rel
% 1.44/1.04  --clausifier_options                    --mode clausify
% 1.44/1.04  --stdin                                 false
% 1.44/1.04  --stats_out                             all
% 1.44/1.04  
% 1.44/1.04  ------ General Options
% 1.44/1.04  
% 1.44/1.04  --fof                                   false
% 1.44/1.04  --time_out_real                         305.
% 1.44/1.04  --time_out_virtual                      -1.
% 1.44/1.04  --symbol_type_check                     false
% 1.44/1.04  --clausify_out                          false
% 1.44/1.04  --sig_cnt_out                           false
% 1.44/1.04  --trig_cnt_out                          false
% 1.44/1.04  --trig_cnt_out_tolerance                1.
% 1.44/1.04  --trig_cnt_out_sk_spl                   false
% 1.44/1.04  --abstr_cl_out                          false
% 1.44/1.04  
% 1.44/1.04  ------ Global Options
% 1.44/1.04  
% 1.44/1.04  --schedule                              default
% 1.44/1.04  --add_important_lit                     false
% 1.44/1.04  --prop_solver_per_cl                    1000
% 1.44/1.04  --min_unsat_core                        false
% 1.44/1.04  --soft_assumptions                      false
% 1.44/1.04  --soft_lemma_size                       3
% 1.44/1.04  --prop_impl_unit_size                   0
% 1.44/1.04  --prop_impl_unit                        []
% 1.44/1.04  --share_sel_clauses                     true
% 1.44/1.04  --reset_solvers                         false
% 1.44/1.04  --bc_imp_inh                            [conj_cone]
% 1.44/1.04  --conj_cone_tolerance                   3.
% 1.44/1.04  --extra_neg_conj                        none
% 1.44/1.04  --large_theory_mode                     true
% 1.44/1.04  --prolific_symb_bound                   200
% 1.44/1.04  --lt_threshold                          2000
% 1.44/1.04  --clause_weak_htbl                      true
% 1.44/1.04  --gc_record_bc_elim                     false
% 1.44/1.04  
% 1.44/1.04  ------ Preprocessing Options
% 1.44/1.04  
% 1.44/1.04  --preprocessing_flag                    true
% 1.44/1.04  --time_out_prep_mult                    0.1
% 1.44/1.04  --splitting_mode                        input
% 1.44/1.04  --splitting_grd                         true
% 1.44/1.04  --splitting_cvd                         false
% 1.44/1.04  --splitting_cvd_svl                     false
% 1.44/1.04  --splitting_nvd                         32
% 1.44/1.04  --sub_typing                            true
% 1.44/1.04  --prep_gs_sim                           true
% 1.44/1.04  --prep_unflatten                        true
% 1.44/1.04  --prep_res_sim                          true
% 1.44/1.04  --prep_upred                            true
% 1.44/1.04  --prep_sem_filter                       exhaustive
% 1.44/1.04  --prep_sem_filter_out                   false
% 1.44/1.04  --pred_elim                             true
% 1.44/1.04  --res_sim_input                         true
% 1.44/1.04  --eq_ax_congr_red                       true
% 1.44/1.04  --pure_diseq_elim                       true
% 1.44/1.04  --brand_transform                       false
% 1.44/1.04  --non_eq_to_eq                          false
% 1.44/1.04  --prep_def_merge                        true
% 1.44/1.04  --prep_def_merge_prop_impl              false
% 1.44/1.04  --prep_def_merge_mbd                    true
% 1.44/1.04  --prep_def_merge_tr_red                 false
% 1.44/1.04  --prep_def_merge_tr_cl                  false
% 1.44/1.04  --smt_preprocessing                     true
% 1.44/1.04  --smt_ac_axioms                         fast
% 1.44/1.04  --preprocessed_out                      false
% 1.44/1.04  --preprocessed_stats                    false
% 1.44/1.04  
% 1.44/1.04  ------ Abstraction refinement Options
% 1.44/1.04  
% 1.44/1.04  --abstr_ref                             []
% 1.44/1.04  --abstr_ref_prep                        false
% 1.44/1.04  --abstr_ref_until_sat                   false
% 1.44/1.04  --abstr_ref_sig_restrict                funpre
% 1.44/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.44/1.04  --abstr_ref_under                       []
% 1.44/1.04  
% 1.44/1.04  ------ SAT Options
% 1.44/1.04  
% 1.44/1.04  --sat_mode                              false
% 1.44/1.04  --sat_fm_restart_options                ""
% 1.44/1.04  --sat_gr_def                            false
% 1.44/1.04  --sat_epr_types                         true
% 1.44/1.04  --sat_non_cyclic_types                  false
% 1.44/1.04  --sat_finite_models                     false
% 1.44/1.04  --sat_fm_lemmas                         false
% 1.44/1.04  --sat_fm_prep                           false
% 1.44/1.04  --sat_fm_uc_incr                        true
% 1.44/1.04  --sat_out_model                         small
% 1.44/1.04  --sat_out_clauses                       false
% 1.44/1.04  
% 1.44/1.04  ------ QBF Options
% 1.44/1.04  
% 1.44/1.04  --qbf_mode                              false
% 1.44/1.04  --qbf_elim_univ                         false
% 1.44/1.04  --qbf_dom_inst                          none
% 1.44/1.04  --qbf_dom_pre_inst                      false
% 1.44/1.04  --qbf_sk_in                             false
% 1.44/1.04  --qbf_pred_elim                         true
% 1.44/1.04  --qbf_split                             512
% 1.44/1.04  
% 1.44/1.04  ------ BMC1 Options
% 1.44/1.04  
% 1.44/1.04  --bmc1_incremental                      false
% 1.44/1.04  --bmc1_axioms                           reachable_all
% 1.44/1.04  --bmc1_min_bound                        0
% 1.44/1.04  --bmc1_max_bound                        -1
% 1.44/1.04  --bmc1_max_bound_default                -1
% 1.44/1.04  --bmc1_symbol_reachability              true
% 1.44/1.04  --bmc1_property_lemmas                  false
% 1.44/1.04  --bmc1_k_induction                      false
% 1.44/1.04  --bmc1_non_equiv_states                 false
% 1.44/1.04  --bmc1_deadlock                         false
% 1.44/1.04  --bmc1_ucm                              false
% 1.44/1.04  --bmc1_add_unsat_core                   none
% 1.44/1.04  --bmc1_unsat_core_children              false
% 1.44/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.44/1.04  --bmc1_out_stat                         full
% 1.44/1.04  --bmc1_ground_init                      false
% 1.44/1.04  --bmc1_pre_inst_next_state              false
% 1.44/1.04  --bmc1_pre_inst_state                   false
% 1.44/1.04  --bmc1_pre_inst_reach_state             false
% 1.44/1.04  --bmc1_out_unsat_core                   false
% 1.44/1.04  --bmc1_aig_witness_out                  false
% 1.44/1.04  --bmc1_verbose                          false
% 1.44/1.04  --bmc1_dump_clauses_tptp                false
% 1.44/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.44/1.04  --bmc1_dump_file                        -
% 1.44/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.44/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.44/1.04  --bmc1_ucm_extend_mode                  1
% 1.44/1.04  --bmc1_ucm_init_mode                    2
% 1.44/1.04  --bmc1_ucm_cone_mode                    none
% 1.44/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.44/1.04  --bmc1_ucm_relax_model                  4
% 1.44/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.44/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.44/1.04  --bmc1_ucm_layered_model                none
% 1.44/1.04  --bmc1_ucm_max_lemma_size               10
% 1.44/1.04  
% 1.44/1.04  ------ AIG Options
% 1.44/1.04  
% 1.44/1.04  --aig_mode                              false
% 1.44/1.04  
% 1.44/1.04  ------ Instantiation Options
% 1.44/1.04  
% 1.44/1.04  --instantiation_flag                    true
% 1.44/1.04  --inst_sos_flag                         false
% 1.44/1.04  --inst_sos_phase                        true
% 1.44/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.44/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.44/1.04  --inst_lit_sel_side                     num_symb
% 1.44/1.04  --inst_solver_per_active                1400
% 1.44/1.04  --inst_solver_calls_frac                1.
% 1.44/1.04  --inst_passive_queue_type               priority_queues
% 1.44/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.44/1.04  --inst_passive_queues_freq              [25;2]
% 1.44/1.04  --inst_dismatching                      true
% 1.44/1.04  --inst_eager_unprocessed_to_passive     true
% 1.44/1.04  --inst_prop_sim_given                   true
% 1.44/1.04  --inst_prop_sim_new                     false
% 1.44/1.04  --inst_subs_new                         false
% 1.44/1.04  --inst_eq_res_simp                      false
% 1.44/1.04  --inst_subs_given                       false
% 1.44/1.04  --inst_orphan_elimination               true
% 1.44/1.04  --inst_learning_loop_flag               true
% 1.44/1.04  --inst_learning_start                   3000
% 1.44/1.04  --inst_learning_factor                  2
% 1.44/1.04  --inst_start_prop_sim_after_learn       3
% 1.44/1.04  --inst_sel_renew                        solver
% 1.44/1.04  --inst_lit_activity_flag                true
% 1.44/1.04  --inst_restr_to_given                   false
% 1.44/1.04  --inst_activity_threshold               500
% 1.44/1.04  --inst_out_proof                        true
% 1.44/1.04  
% 1.44/1.04  ------ Resolution Options
% 1.44/1.04  
% 1.44/1.04  --resolution_flag                       true
% 1.44/1.04  --res_lit_sel                           adaptive
% 1.44/1.04  --res_lit_sel_side                      none
% 1.44/1.04  --res_ordering                          kbo
% 1.44/1.04  --res_to_prop_solver                    active
% 1.44/1.04  --res_prop_simpl_new                    false
% 1.44/1.04  --res_prop_simpl_given                  true
% 1.44/1.04  --res_passive_queue_type                priority_queues
% 1.44/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.44/1.04  --res_passive_queues_freq               [15;5]
% 1.44/1.04  --res_forward_subs                      full
% 1.44/1.04  --res_backward_subs                     full
% 1.44/1.04  --res_forward_subs_resolution           true
% 1.44/1.04  --res_backward_subs_resolution          true
% 1.44/1.04  --res_orphan_elimination                true
% 1.44/1.04  --res_time_limit                        2.
% 1.44/1.04  --res_out_proof                         true
% 1.44/1.04  
% 1.44/1.04  ------ Superposition Options
% 1.44/1.04  
% 1.44/1.04  --superposition_flag                    true
% 1.44/1.04  --sup_passive_queue_type                priority_queues
% 1.44/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.44/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.44/1.04  --demod_completeness_check              fast
% 1.44/1.04  --demod_use_ground                      true
% 1.44/1.04  --sup_to_prop_solver                    passive
% 1.44/1.04  --sup_prop_simpl_new                    true
% 1.44/1.04  --sup_prop_simpl_given                  true
% 1.44/1.04  --sup_fun_splitting                     false
% 1.44/1.04  --sup_smt_interval                      50000
% 1.44/1.04  
% 1.44/1.04  ------ Superposition Simplification Setup
% 1.44/1.04  
% 1.44/1.04  --sup_indices_passive                   []
% 1.44/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.44/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.04  --sup_full_bw                           [BwDemod]
% 1.44/1.04  --sup_immed_triv                        [TrivRules]
% 1.44/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.44/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.04  --sup_immed_bw_main                     []
% 1.44/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.44/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/1.04  
% 1.44/1.04  ------ Combination Options
% 1.44/1.04  
% 1.44/1.04  --comb_res_mult                         3
% 1.44/1.04  --comb_sup_mult                         2
% 1.44/1.04  --comb_inst_mult                        10
% 1.44/1.04  
% 1.44/1.04  ------ Debug Options
% 1.44/1.04  
% 1.44/1.04  --dbg_backtrace                         false
% 1.44/1.04  --dbg_dump_prop_clauses                 false
% 1.44/1.04  --dbg_dump_prop_clauses_file            -
% 1.44/1.04  --dbg_out_stat                          false
% 1.44/1.04  ------ Parsing...
% 1.44/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.44/1.04  
% 1.44/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.44/1.04  
% 1.44/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.44/1.04  
% 1.44/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.44/1.04  ------ Proving...
% 1.44/1.04  ------ Problem Properties 
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  clauses                                 13
% 1.44/1.04  conjectures                             2
% 1.44/1.04  EPR                                     1
% 1.44/1.04  Horn                                    10
% 1.44/1.04  unary                                   4
% 1.44/1.04  binary                                  4
% 1.44/1.04  lits                                    35
% 1.44/1.04  lits eq                                 8
% 1.44/1.04  fd_pure                                 0
% 1.44/1.04  fd_pseudo                               0
% 1.44/1.04  fd_cond                                 0
% 1.44/1.04  fd_pseudo_cond                          0
% 1.44/1.04  AC symbols                              0
% 1.44/1.04  
% 1.44/1.04  ------ Schedule dynamic 5 is on 
% 1.44/1.04  
% 1.44/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  ------ 
% 1.44/1.04  Current options:
% 1.44/1.04  ------ 
% 1.44/1.04  
% 1.44/1.04  ------ Input Options
% 1.44/1.04  
% 1.44/1.04  --out_options                           all
% 1.44/1.04  --tptp_safe_out                         true
% 1.44/1.04  --problem_path                          ""
% 1.44/1.04  --include_path                          ""
% 1.44/1.04  --clausifier                            res/vclausify_rel
% 1.44/1.04  --clausifier_options                    --mode clausify
% 1.44/1.04  --stdin                                 false
% 1.44/1.04  --stats_out                             all
% 1.44/1.04  
% 1.44/1.04  ------ General Options
% 1.44/1.04  
% 1.44/1.04  --fof                                   false
% 1.44/1.04  --time_out_real                         305.
% 1.44/1.04  --time_out_virtual                      -1.
% 1.44/1.04  --symbol_type_check                     false
% 1.44/1.04  --clausify_out                          false
% 1.44/1.04  --sig_cnt_out                           false
% 1.44/1.04  --trig_cnt_out                          false
% 1.44/1.04  --trig_cnt_out_tolerance                1.
% 1.44/1.04  --trig_cnt_out_sk_spl                   false
% 1.44/1.04  --abstr_cl_out                          false
% 1.44/1.04  
% 1.44/1.04  ------ Global Options
% 1.44/1.04  
% 1.44/1.04  --schedule                              default
% 1.44/1.04  --add_important_lit                     false
% 1.44/1.04  --prop_solver_per_cl                    1000
% 1.44/1.04  --min_unsat_core                        false
% 1.44/1.04  --soft_assumptions                      false
% 1.44/1.04  --soft_lemma_size                       3
% 1.44/1.04  --prop_impl_unit_size                   0
% 1.44/1.04  --prop_impl_unit                        []
% 1.44/1.04  --share_sel_clauses                     true
% 1.44/1.04  --reset_solvers                         false
% 1.44/1.04  --bc_imp_inh                            [conj_cone]
% 1.44/1.04  --conj_cone_tolerance                   3.
% 1.44/1.04  --extra_neg_conj                        none
% 1.44/1.04  --large_theory_mode                     true
% 1.44/1.04  --prolific_symb_bound                   200
% 1.44/1.04  --lt_threshold                          2000
% 1.44/1.04  --clause_weak_htbl                      true
% 1.44/1.04  --gc_record_bc_elim                     false
% 1.44/1.04  
% 1.44/1.04  ------ Preprocessing Options
% 1.44/1.04  
% 1.44/1.04  --preprocessing_flag                    true
% 1.44/1.04  --time_out_prep_mult                    0.1
% 1.44/1.04  --splitting_mode                        input
% 1.44/1.04  --splitting_grd                         true
% 1.44/1.04  --splitting_cvd                         false
% 1.44/1.04  --splitting_cvd_svl                     false
% 1.44/1.04  --splitting_nvd                         32
% 1.44/1.04  --sub_typing                            true
% 1.44/1.04  --prep_gs_sim                           true
% 1.44/1.04  --prep_unflatten                        true
% 1.44/1.04  --prep_res_sim                          true
% 1.44/1.04  --prep_upred                            true
% 1.44/1.04  --prep_sem_filter                       exhaustive
% 1.44/1.04  --prep_sem_filter_out                   false
% 1.44/1.04  --pred_elim                             true
% 1.44/1.04  --res_sim_input                         true
% 1.44/1.04  --eq_ax_congr_red                       true
% 1.44/1.04  --pure_diseq_elim                       true
% 1.44/1.04  --brand_transform                       false
% 1.44/1.04  --non_eq_to_eq                          false
% 1.44/1.04  --prep_def_merge                        true
% 1.44/1.04  --prep_def_merge_prop_impl              false
% 1.44/1.04  --prep_def_merge_mbd                    true
% 1.44/1.04  --prep_def_merge_tr_red                 false
% 1.44/1.04  --prep_def_merge_tr_cl                  false
% 1.44/1.04  --smt_preprocessing                     true
% 1.44/1.04  --smt_ac_axioms                         fast
% 1.44/1.04  --preprocessed_out                      false
% 1.44/1.04  --preprocessed_stats                    false
% 1.44/1.04  
% 1.44/1.04  ------ Abstraction refinement Options
% 1.44/1.04  
% 1.44/1.04  --abstr_ref                             []
% 1.44/1.04  --abstr_ref_prep                        false
% 1.44/1.04  --abstr_ref_until_sat                   false
% 1.44/1.04  --abstr_ref_sig_restrict                funpre
% 1.44/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.44/1.04  --abstr_ref_under                       []
% 1.44/1.04  
% 1.44/1.04  ------ SAT Options
% 1.44/1.04  
% 1.44/1.04  --sat_mode                              false
% 1.44/1.04  --sat_fm_restart_options                ""
% 1.44/1.04  --sat_gr_def                            false
% 1.44/1.04  --sat_epr_types                         true
% 1.44/1.04  --sat_non_cyclic_types                  false
% 1.44/1.04  --sat_finite_models                     false
% 1.44/1.04  --sat_fm_lemmas                         false
% 1.44/1.04  --sat_fm_prep                           false
% 1.44/1.04  --sat_fm_uc_incr                        true
% 1.44/1.04  --sat_out_model                         small
% 1.44/1.04  --sat_out_clauses                       false
% 1.44/1.04  
% 1.44/1.04  ------ QBF Options
% 1.44/1.04  
% 1.44/1.04  --qbf_mode                              false
% 1.44/1.04  --qbf_elim_univ                         false
% 1.44/1.04  --qbf_dom_inst                          none
% 1.44/1.04  --qbf_dom_pre_inst                      false
% 1.44/1.04  --qbf_sk_in                             false
% 1.44/1.04  --qbf_pred_elim                         true
% 1.44/1.04  --qbf_split                             512
% 1.44/1.04  
% 1.44/1.04  ------ BMC1 Options
% 1.44/1.04  
% 1.44/1.04  --bmc1_incremental                      false
% 1.44/1.04  --bmc1_axioms                           reachable_all
% 1.44/1.04  --bmc1_min_bound                        0
% 1.44/1.04  --bmc1_max_bound                        -1
% 1.44/1.04  --bmc1_max_bound_default                -1
% 1.44/1.04  --bmc1_symbol_reachability              true
% 1.44/1.04  --bmc1_property_lemmas                  false
% 1.44/1.04  --bmc1_k_induction                      false
% 1.44/1.04  --bmc1_non_equiv_states                 false
% 1.44/1.04  --bmc1_deadlock                         false
% 1.44/1.04  --bmc1_ucm                              false
% 1.44/1.04  --bmc1_add_unsat_core                   none
% 1.44/1.04  --bmc1_unsat_core_children              false
% 1.44/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.44/1.04  --bmc1_out_stat                         full
% 1.44/1.04  --bmc1_ground_init                      false
% 1.44/1.04  --bmc1_pre_inst_next_state              false
% 1.44/1.04  --bmc1_pre_inst_state                   false
% 1.44/1.04  --bmc1_pre_inst_reach_state             false
% 1.44/1.04  --bmc1_out_unsat_core                   false
% 1.44/1.04  --bmc1_aig_witness_out                  false
% 1.44/1.04  --bmc1_verbose                          false
% 1.44/1.04  --bmc1_dump_clauses_tptp                false
% 1.44/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.44/1.04  --bmc1_dump_file                        -
% 1.44/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.44/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.44/1.04  --bmc1_ucm_extend_mode                  1
% 1.44/1.04  --bmc1_ucm_init_mode                    2
% 1.44/1.04  --bmc1_ucm_cone_mode                    none
% 1.44/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.44/1.04  --bmc1_ucm_relax_model                  4
% 1.44/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.44/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.44/1.04  --bmc1_ucm_layered_model                none
% 1.44/1.04  --bmc1_ucm_max_lemma_size               10
% 1.44/1.04  
% 1.44/1.04  ------ AIG Options
% 1.44/1.04  
% 1.44/1.04  --aig_mode                              false
% 1.44/1.04  
% 1.44/1.04  ------ Instantiation Options
% 1.44/1.04  
% 1.44/1.04  --instantiation_flag                    true
% 1.44/1.04  --inst_sos_flag                         false
% 1.44/1.04  --inst_sos_phase                        true
% 1.44/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.44/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.44/1.04  --inst_lit_sel_side                     none
% 1.44/1.04  --inst_solver_per_active                1400
% 1.44/1.04  --inst_solver_calls_frac                1.
% 1.44/1.04  --inst_passive_queue_type               priority_queues
% 1.44/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.44/1.04  --inst_passive_queues_freq              [25;2]
% 1.44/1.04  --inst_dismatching                      true
% 1.44/1.04  --inst_eager_unprocessed_to_passive     true
% 1.44/1.04  --inst_prop_sim_given                   true
% 1.44/1.04  --inst_prop_sim_new                     false
% 1.44/1.04  --inst_subs_new                         false
% 1.44/1.04  --inst_eq_res_simp                      false
% 1.44/1.04  --inst_subs_given                       false
% 1.44/1.04  --inst_orphan_elimination               true
% 1.44/1.04  --inst_learning_loop_flag               true
% 1.44/1.04  --inst_learning_start                   3000
% 1.44/1.04  --inst_learning_factor                  2
% 1.44/1.04  --inst_start_prop_sim_after_learn       3
% 1.44/1.04  --inst_sel_renew                        solver
% 1.44/1.04  --inst_lit_activity_flag                true
% 1.44/1.04  --inst_restr_to_given                   false
% 1.44/1.04  --inst_activity_threshold               500
% 1.44/1.04  --inst_out_proof                        true
% 1.44/1.04  
% 1.44/1.04  ------ Resolution Options
% 1.44/1.04  
% 1.44/1.04  --resolution_flag                       false
% 1.44/1.04  --res_lit_sel                           adaptive
% 1.44/1.04  --res_lit_sel_side                      none
% 1.44/1.04  --res_ordering                          kbo
% 1.44/1.04  --res_to_prop_solver                    active
% 1.44/1.04  --res_prop_simpl_new                    false
% 1.44/1.04  --res_prop_simpl_given                  true
% 1.44/1.04  --res_passive_queue_type                priority_queues
% 1.44/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.44/1.04  --res_passive_queues_freq               [15;5]
% 1.44/1.04  --res_forward_subs                      full
% 1.44/1.04  --res_backward_subs                     full
% 1.44/1.04  --res_forward_subs_resolution           true
% 1.44/1.04  --res_backward_subs_resolution          true
% 1.44/1.04  --res_orphan_elimination                true
% 1.44/1.04  --res_time_limit                        2.
% 1.44/1.04  --res_out_proof                         true
% 1.44/1.04  
% 1.44/1.04  ------ Superposition Options
% 1.44/1.04  
% 1.44/1.04  --superposition_flag                    true
% 1.44/1.04  --sup_passive_queue_type                priority_queues
% 1.44/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.44/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.44/1.04  --demod_completeness_check              fast
% 1.44/1.04  --demod_use_ground                      true
% 1.44/1.04  --sup_to_prop_solver                    passive
% 1.44/1.04  --sup_prop_simpl_new                    true
% 1.44/1.04  --sup_prop_simpl_given                  true
% 1.44/1.04  --sup_fun_splitting                     false
% 1.44/1.04  --sup_smt_interval                      50000
% 1.44/1.04  
% 1.44/1.04  ------ Superposition Simplification Setup
% 1.44/1.04  
% 1.44/1.04  --sup_indices_passive                   []
% 1.44/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.44/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.04  --sup_full_bw                           [BwDemod]
% 1.44/1.04  --sup_immed_triv                        [TrivRules]
% 1.44/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.44/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.04  --sup_immed_bw_main                     []
% 1.44/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.44/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/1.04  
% 1.44/1.04  ------ Combination Options
% 1.44/1.04  
% 1.44/1.04  --comb_res_mult                         3
% 1.44/1.04  --comb_sup_mult                         2
% 1.44/1.04  --comb_inst_mult                        10
% 1.44/1.04  
% 1.44/1.04  ------ Debug Options
% 1.44/1.04  
% 1.44/1.04  --dbg_backtrace                         false
% 1.44/1.04  --dbg_dump_prop_clauses                 false
% 1.44/1.04  --dbg_dump_prop_clauses_file            -
% 1.44/1.04  --dbg_out_stat                          false
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  ------ Proving...
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  % SZS status Theorem for theBenchmark.p
% 1.44/1.04  
% 1.44/1.04   Resolution empty clause
% 1.44/1.04  
% 1.44/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.44/1.04  
% 1.44/1.04  fof(f1,axiom,(
% 1.44/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f18,plain,(
% 1.44/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.44/1.04    inference(ennf_transformation,[],[f1])).
% 1.44/1.04  
% 1.44/1.04  fof(f35,plain,(
% 1.44/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/1.04    inference(nnf_transformation,[],[f18])).
% 1.44/1.04  
% 1.44/1.04  fof(f36,plain,(
% 1.44/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/1.04    inference(rectify,[],[f35])).
% 1.44/1.04  
% 1.44/1.04  fof(f37,plain,(
% 1.44/1.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.44/1.04    introduced(choice_axiom,[])).
% 1.44/1.04  
% 1.44/1.04  fof(f38,plain,(
% 1.44/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 1.44/1.04  
% 1.44/1.04  fof(f48,plain,(
% 1.44/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f38])).
% 1.44/1.04  
% 1.44/1.04  fof(f49,plain,(
% 1.44/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f38])).
% 1.44/1.04  
% 1.44/1.04  fof(f2,axiom,(
% 1.44/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f39,plain,(
% 1.44/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.44/1.04    inference(nnf_transformation,[],[f2])).
% 1.44/1.04  
% 1.44/1.04  fof(f51,plain,(
% 1.44/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f39])).
% 1.44/1.04  
% 1.44/1.04  fof(f12,conjecture,(
% 1.44/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f13,negated_conjecture,(
% 1.44/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.44/1.04    inference(negated_conjecture,[],[f12])).
% 1.44/1.04  
% 1.44/1.04  fof(f33,plain,(
% 1.44/1.04    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.44/1.04    inference(ennf_transformation,[],[f13])).
% 1.44/1.04  
% 1.44/1.04  fof(f34,plain,(
% 1.44/1.04    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/1.04    inference(flattening,[],[f33])).
% 1.44/1.04  
% 1.44/1.04  fof(f41,plain,(
% 1.44/1.04    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/1.04    inference(nnf_transformation,[],[f34])).
% 1.44/1.04  
% 1.44/1.04  fof(f42,plain,(
% 1.44/1.04    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/1.04    inference(flattening,[],[f41])).
% 1.44/1.04  
% 1.44/1.04  fof(f45,plain,(
% 1.44/1.04    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK3) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3)) & (r1_waybel_7(X0,X1,sK3) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.44/1.04    introduced(choice_axiom,[])).
% 1.44/1.04  
% 1.44/1.04  fof(f44,plain,(
% 1.44/1.04    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK2,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2)) & (r1_waybel_7(X0,sK2,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2))) )),
% 1.44/1.04    introduced(choice_axiom,[])).
% 1.44/1.04  
% 1.44/1.04  fof(f43,plain,(
% 1.44/1.04    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK1,X1,X2) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2)) & (r1_waybel_7(sK1,X1,X2) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.44/1.04    introduced(choice_axiom,[])).
% 1.44/1.04  
% 1.44/1.04  fof(f46,plain,(
% 1.44/1.04    (((~r1_waybel_7(sK1,sK2,sK3) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)) & (r1_waybel_7(sK1,sK2,sK3) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.44/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f45,f44,f43])).
% 1.44/1.04  
% 1.44/1.04  fof(f70,plain,(
% 1.44/1.04    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f6,axiom,(
% 1.44/1.04    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f55,plain,(
% 1.44/1.04    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.44/1.04    inference(cnf_transformation,[],[f6])).
% 1.44/1.04  
% 1.44/1.04  fof(f85,plain,(
% 1.44/1.04    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 1.44/1.04    inference(definition_unfolding,[],[f70,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f7,axiom,(
% 1.44/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f16,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.44/1.04    inference(pure_predicate_removal,[],[f7])).
% 1.44/1.04  
% 1.44/1.04  fof(f23,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/1.04    inference(ennf_transformation,[],[f16])).
% 1.44/1.04  
% 1.44/1.04  fof(f24,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.44/1.04    inference(flattening,[],[f23])).
% 1.44/1.04  
% 1.44/1.04  fof(f57,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f24])).
% 1.44/1.04  
% 1.44/1.04  fof(f76,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(definition_unfolding,[],[f57,f55,f55,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f75,plain,(
% 1.44/1.04    ~r1_waybel_7(sK1,sK2,sK3) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f10,axiom,(
% 1.44/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f29,plain,(
% 1.44/1.04    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/1.04    inference(ennf_transformation,[],[f10])).
% 1.44/1.04  
% 1.44/1.04  fof(f30,plain,(
% 1.44/1.04    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/1.04    inference(flattening,[],[f29])).
% 1.44/1.04  
% 1.44/1.04  fof(f40,plain,(
% 1.44/1.04    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/1.04    inference(nnf_transformation,[],[f30])).
% 1.44/1.04  
% 1.44/1.04  fof(f63,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f40])).
% 1.44/1.04  
% 1.44/1.04  fof(f66,plain,(
% 1.44/1.04    v2_pre_topc(sK1)),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f65,plain,(
% 1.44/1.04    ~v2_struct_0(sK1)),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f67,plain,(
% 1.44/1.04    l1_pre_topc(sK1)),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f73,plain,(
% 1.44/1.04    m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f4,axiom,(
% 1.44/1.04    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f20,plain,(
% 1.44/1.04    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.44/1.04    inference(ennf_transformation,[],[f4])).
% 1.44/1.04  
% 1.44/1.04  fof(f53,plain,(
% 1.44/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f20])).
% 1.44/1.04  
% 1.44/1.04  fof(f71,plain,(
% 1.44/1.04    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f84,plain,(
% 1.44/1.04    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 1.44/1.04    inference(definition_unfolding,[],[f71,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f68,plain,(
% 1.44/1.04    ~v1_xboole_0(sK2)),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f5,axiom,(
% 1.44/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f21,plain,(
% 1.44/1.04    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/1.04    inference(ennf_transformation,[],[f5])).
% 1.44/1.04  
% 1.44/1.04  fof(f22,plain,(
% 1.44/1.04    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.44/1.04    inference(flattening,[],[f21])).
% 1.44/1.04  
% 1.44/1.04  fof(f54,plain,(
% 1.44/1.04    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f22])).
% 1.44/1.04  
% 1.44/1.04  fof(f72,plain,(
% 1.44/1.04    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f83,plain,(
% 1.44/1.04    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))),
% 1.44/1.04    inference(definition_unfolding,[],[f72,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f56,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f24])).
% 1.44/1.04  
% 1.44/1.04  fof(f77,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(definition_unfolding,[],[f56,f55,f55,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f8,axiom,(
% 1.44/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f14,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.44/1.04    inference(pure_predicate_removal,[],[f8])).
% 1.44/1.04  
% 1.44/1.04  fof(f15,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.44/1.04    inference(pure_predicate_removal,[],[f14])).
% 1.44/1.04  
% 1.44/1.04  fof(f25,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/1.04    inference(ennf_transformation,[],[f15])).
% 1.44/1.04  
% 1.44/1.04  fof(f26,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.44/1.04    inference(flattening,[],[f25])).
% 1.44/1.04  
% 1.44/1.04  fof(f59,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f26])).
% 1.44/1.04  
% 1.44/1.04  fof(f78,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(definition_unfolding,[],[f59,f55,f55,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f9,axiom,(
% 1.44/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f17,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.44/1.04    inference(pure_predicate_removal,[],[f9])).
% 1.44/1.04  
% 1.44/1.04  fof(f27,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/1.04    inference(ennf_transformation,[],[f17])).
% 1.44/1.04  
% 1.44/1.04  fof(f28,plain,(
% 1.44/1.04    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.44/1.04    inference(flattening,[],[f27])).
% 1.44/1.04  
% 1.44/1.04  fof(f61,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f28])).
% 1.44/1.04  
% 1.44/1.04  fof(f80,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(definition_unfolding,[],[f61,f55,f55,f55,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f69,plain,(
% 1.44/1.04    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f86,plain,(
% 1.44/1.04    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))),
% 1.44/1.04    inference(definition_unfolding,[],[f69,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f11,axiom,(
% 1.44/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f31,plain,(
% 1.44/1.04    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/1.04    inference(ennf_transformation,[],[f11])).
% 1.44/1.04  
% 1.44/1.04  fof(f32,plain,(
% 1.44/1.04    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.44/1.04    inference(flattening,[],[f31])).
% 1.44/1.04  
% 1.44/1.04  fof(f64,plain,(
% 1.44/1.04    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f32])).
% 1.44/1.04  
% 1.44/1.04  fof(f82,plain,(
% 1.44/1.04    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(definition_unfolding,[],[f64,f55,f55,f55,f55])).
% 1.44/1.04  
% 1.44/1.04  fof(f3,axiom,(
% 1.44/1.04    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.44/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.04  
% 1.44/1.04  fof(f19,plain,(
% 1.44/1.04    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.44/1.04    inference(ennf_transformation,[],[f3])).
% 1.44/1.04  
% 1.44/1.04  fof(f52,plain,(
% 1.44/1.04    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f19])).
% 1.44/1.04  
% 1.44/1.04  fof(f74,plain,(
% 1.44/1.04    r1_waybel_7(sK1,sK2,sK3) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)),
% 1.44/1.04    inference(cnf_transformation,[],[f46])).
% 1.44/1.04  
% 1.44/1.04  fof(f62,plain,(
% 1.44/1.04    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/1.04    inference(cnf_transformation,[],[f40])).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1,plain,
% 1.44/1.04      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.44/1.04      inference(cnf_transformation,[],[f48]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3762,plain,
% 1.44/1.04      ( r2_hidden(sK0(X0_55,X1_55),X0_55) | r1_tarski(X0_55,X1_55) ),
% 1.44/1.04      inference(subtyping,[status(esa)],[c_1]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4132,plain,
% 1.44/1.04      ( r2_hidden(sK0(X0_55,X1_55),X0_55) = iProver_top
% 1.44/1.04      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 1.44/1.04      inference(predicate_to_equality,[status(thm)],[c_3762]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_0,plain,
% 1.44/1.04      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.44/1.04      inference(cnf_transformation,[],[f49]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3763,plain,
% 1.44/1.04      ( ~ r2_hidden(sK0(X0_55,X1_55),X1_55) | r1_tarski(X0_55,X1_55) ),
% 1.44/1.04      inference(subtyping,[status(esa)],[c_0]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4131,plain,
% 1.44/1.04      ( r2_hidden(sK0(X0_55,X1_55),X1_55) != iProver_top
% 1.44/1.04      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 1.44/1.04      inference(predicate_to_equality,[status(thm)],[c_3763]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4438,plain,
% 1.44/1.04      ( r1_tarski(X0_55,X0_55) = iProver_top ),
% 1.44/1.04      inference(superposition,[status(thm)],[c_4132,c_4131]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3,plain,
% 1.44/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.44/1.04      inference(cnf_transformation,[],[f51]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3760,plain,
% 1.44/1.04      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) | ~ r1_tarski(X0_55,X1_55) ),
% 1.44/1.04      inference(subtyping,[status(esa)],[c_3]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4134,plain,
% 1.44/1.04      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) = iProver_top
% 1.44/1.04      | r1_tarski(X0_55,X1_55) != iProver_top ),
% 1.44/1.04      inference(predicate_to_equality,[status(thm)],[c_3760]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_22,negated_conjecture,
% 1.44/1.04      ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(cnf_transformation,[],[f85]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_8,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X2) ),
% 1.44/1.04      inference(cnf_transformation,[],[f76]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_17,negated_conjecture,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 1.44/1.04      inference(cnf_transformation,[],[f75]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_212,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 1.44/1.04      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_14,plain,
% 1.44/1.04      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.44/1.04      | r3_waybel_9(X0,X1,X2)
% 1.44/1.04      | ~ l1_waybel_0(X1,X0)
% 1.44/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.44/1.04      | ~ v2_pre_topc(X0)
% 1.44/1.04      | ~ v7_waybel_0(X1)
% 1.44/1.04      | ~ v4_orders_2(X1)
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | ~ l1_pre_topc(X0) ),
% 1.44/1.04      inference(cnf_transformation,[],[f63]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_26,negated_conjecture,
% 1.44/1.04      ( v2_pre_topc(sK1) ),
% 1.44/1.04      inference(cnf_transformation,[],[f66]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_577,plain,
% 1.44/1.04      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.44/1.04      | r3_waybel_9(X0,X1,X2)
% 1.44/1.04      | ~ l1_waybel_0(X1,X0)
% 1.44/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.44/1.04      | ~ v7_waybel_0(X1)
% 1.44/1.04      | ~ v4_orders_2(X1)
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | ~ l1_pre_topc(X0)
% 1.44/1.04      | sK1 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_578,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.44/1.04      | r3_waybel_9(sK1,X0,X1)
% 1.44/1.04      | ~ l1_waybel_0(X0,sK1)
% 1.44/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.44/1.04      | ~ v7_waybel_0(X0)
% 1.44/1.04      | ~ v4_orders_2(X0)
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | v2_struct_0(sK1)
% 1.44/1.04      | ~ l1_pre_topc(sK1) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_577]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_27,negated_conjecture,
% 1.44/1.04      ( ~ v2_struct_0(sK1) ),
% 1.44/1.04      inference(cnf_transformation,[],[f65]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_25,negated_conjecture,
% 1.44/1.04      ( l1_pre_topc(sK1) ),
% 1.44/1.04      inference(cnf_transformation,[],[f67]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_582,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.44/1.04      | r3_waybel_9(sK1,X0,X1)
% 1.44/1.04      | ~ l1_waybel_0(X0,sK1)
% 1.44/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.44/1.04      | ~ v7_waybel_0(X0)
% 1.44/1.04      | ~ v4_orders_2(X0)
% 1.44/1.04      | v2_struct_0(X0) ),
% 1.44/1.04      inference(global_propositional_subsumption,
% 1.44/1.04                [status(thm)],
% 1.44/1.04                [c_578,c_27,c_25]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_955,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ l1_waybel_0(X0,sK1)
% 1.44/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.44/1.04      | ~ v7_waybel_0(X0)
% 1.44/1.04      | ~ v4_orders_2(X0)
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
% 1.44/1.04      | sK3 != X1
% 1.44/1.04      | sK1 != sK1 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_212,c_582]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_956,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 1.44/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_955]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_19,negated_conjecture,
% 1.44/1.04      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 1.44/1.04      inference(cnf_transformation,[],[f73]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_958,plain,
% 1.44/1.04      ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_956,c_19]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_959,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_958]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_995,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X2)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
% 1.44/1.04      | sK1 != X2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_959]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_996,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(sK1)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(sK1)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_995]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_6,plain,
% 1.44/1.04      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.44/1.04      inference(cnf_transformation,[],[f53]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_68,plain,
% 1.44/1.04      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 1.44/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1000,plain,
% 1.44/1.04      ( v1_xboole_0(X0)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 1.44/1.04      inference(global_propositional_subsumption,
% 1.44/1.04                [status(thm)],
% 1.44/1.04                [c_996,c_27,c_25,c_68]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1001,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1000]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_21,negated_conjecture,
% 1.44/1.04      ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(cnf_transformation,[],[f84]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1589,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.44/1.04      | sK2 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_1001,c_21]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1590,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | v1_xboole_0(sK2)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1589]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_24,negated_conjecture,
% 1.44/1.04      ( ~ v1_xboole_0(sK2) ),
% 1.44/1.04      inference(cnf_transformation,[],[f68]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1594,plain,
% 1.44/1.04      ( v1_xboole_0(X0)
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1590,c_24]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1595,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1594]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1938,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_1595]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_7,plain,
% 1.44/1.04      ( v2_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.44/1.04      inference(cnf_transformation,[],[f54]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_626,plain,
% 1.44/1.04      ( l1_struct_0(X0) | sK1 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_627,plain,
% 1.44/1.04      ( l1_struct_0(sK1) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_626]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1104,plain,
% 1.44/1.04      ( v2_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_627]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1105,plain,
% 1.44/1.04      ( v2_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1104]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_65,plain,
% 1.44/1.04      ( v2_struct_0(sK1)
% 1.44/1.04      | ~ v1_xboole_0(k2_struct_0(sK1))
% 1.44/1.04      | ~ l1_struct_0(sK1) ),
% 1.44/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1107,plain,
% 1.44/1.04      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.44/1.04      inference(global_propositional_subsumption,
% 1.44/1.04                [status(thm)],
% 1.44/1.04                [c_1105,c_27,c_25,c_65,c_68]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2639,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | k2_struct_0(sK1) != X0
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_1938,c_1107]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2640,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_2639]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_20,negated_conjecture,
% 1.44/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
% 1.44/1.04      inference(cnf_transformation,[],[f83]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_9,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X2) ),
% 1.44/1.04      inference(cnf_transformation,[],[f77]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1153,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | sK1 != X2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_627]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1154,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 1.44/1.04      | v2_struct_0(sK1)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1153]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1158,plain,
% 1.44/1.04      ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1154,c_27]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1159,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1158]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1484,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.44/1.04      | sK2 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_1159,c_21]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1485,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | v1_xboole_0(sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1484]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1489,plain,
% 1.44/1.04      ( v1_xboole_0(X0)
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1485,c_24]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1490,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1489]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2037,plain,
% 1.44/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_1490]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2579,plain,
% 1.44/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | k2_struct_0(sK1) != X0
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_2037,c_1107]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2580,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_2579]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2582,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_2580,c_20]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_10,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X2) ),
% 1.44/1.04      inference(cnf_transformation,[],[f78]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1120,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | sK1 != X2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_627]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1121,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 1.44/1.04      | v2_struct_0(sK1)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1120]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1125,plain,
% 1.44/1.04      ( v4_orders_2(k3_yellow19(sK1,X1,X0))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1121,c_27]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1126,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1125]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1514,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.44/1.04      | sK2 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_1126,c_21]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1515,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | v1_xboole_0(sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1514]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1519,plain,
% 1.44/1.04      ( v1_xboole_0(X0)
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1515,c_24]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1520,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1519]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2014,plain,
% 1.44/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_1520]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2596,plain,
% 1.44/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | k2_struct_0(sK1) != X0
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_2014,c_1107]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2597,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_2596]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2599,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_2597,c_20]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2642,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(global_propositional_subsumption,
% 1.44/1.04                [status(thm)],
% 1.44/1.04                [c_2640,c_20,c_2582,c_2599]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2643,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_2642]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3307,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(equality_resolution_simp,[status(thm)],[c_2643]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_12,plain,
% 1.44/1.04      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X2) ),
% 1.44/1.04      inference(cnf_transformation,[],[f80]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_23,negated_conjecture,
% 1.44/1.04      ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
% 1.44/1.04      inference(cnf_transformation,[],[f86]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_454,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X2)
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | sK2 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_455,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | v1_xboole_0(sK2)
% 1.44/1.04      | ~ l1_struct_0(X1)
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_454]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_459,plain,
% 1.44/1.04      ( v1_xboole_0(X0)
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ l1_struct_0(X1)
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_455,c_24]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_460,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X1)
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_459]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1186,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | sK1 != X1 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_460,c_627]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1187,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v2_struct_0(sK1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1186]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1191,plain,
% 1.44/1.04      ( v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1187,c_27]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1192,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1191]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1634,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_21,c_1192]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1912,plain,
% 1.44/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_1634]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2665,plain,
% 1.44/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | k2_struct_0(sK1) != X0
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_1912,c_1107]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2666,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_2665]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2668,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_2666,c_20]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3305,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(equality_resolution_simp,[status(thm)],[c_2668]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3309,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_3307,c_3305]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3310,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_3309]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3753,plain,
% 1.44/1.04      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.44/1.04      inference(subtyping,[status(esa)],[c_3310]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4140,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) != iProver_top
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 1.44/1.04      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.44/1.04      inference(predicate_to_equality,[status(thm)],[c_3753]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_16,plain,
% 1.44/1.04      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X1)
% 1.44/1.04      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.44/1.04      inference(cnf_transformation,[],[f82]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_493,plain,
% 1.44/1.04      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X1)
% 1.44/1.04      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.44/1.04      | sK2 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_494,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | v1_xboole_0(sK2)
% 1.44/1.04      | ~ l1_struct_0(X0)
% 1.44/1.04      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_493]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_498,plain,
% 1.44/1.04      ( v2_struct_0(X0)
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.44/1.04      | ~ l1_struct_0(X0)
% 1.44/1.04      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_494,c_24]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_499,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X0)
% 1.44/1.04      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_498]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1093,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.44/1.04      | sK1 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_499,c_627]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1094,plain,
% 1.44/1.04      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.44/1.04      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.44/1.04      | v2_struct_0(sK1)
% 1.44/1.04      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1093]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1096,plain,
% 1.44/1.04      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
% 1.44/1.04      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.44/1.04      inference(global_propositional_subsumption,
% 1.44/1.04                [status(thm)],
% 1.44/1.04                [c_1094,c_27,c_22,c_21,c_20]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3320,plain,
% 1.44/1.04      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
% 1.44/1.04      inference(equality_resolution_simp,[status(thm)],[c_1096]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3751,plain,
% 1.44/1.04      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
% 1.44/1.04      inference(subtyping,[status(esa)],[c_3320]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_5,plain,
% 1.44/1.04      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.44/1.04      inference(cnf_transformation,[],[f52]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1115,plain,
% 1.44/1.04      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_5,c_627]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1116,plain,
% 1.44/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1115]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3756,plain,
% 1.44/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.44/1.04      inference(subtyping,[status(esa)],[c_1116]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4178,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 1.44/1.04      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.44/1.04      inference(light_normalisation,[status(thm)],[c_4140,c_3751,c_3756]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_18,negated_conjecture,
% 1.44/1.04      ( r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 1.44/1.04      inference(cnf_transformation,[],[f74]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_214,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 1.44/1.04      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_15,plain,
% 1.44/1.04      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.44/1.04      | ~ r3_waybel_9(X0,X1,X2)
% 1.44/1.04      | ~ l1_waybel_0(X1,X0)
% 1.44/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.44/1.04      | ~ v2_pre_topc(X0)
% 1.44/1.04      | ~ v7_waybel_0(X1)
% 1.44/1.04      | ~ v4_orders_2(X1)
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | ~ l1_pre_topc(X0) ),
% 1.44/1.04      inference(cnf_transformation,[],[f62]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_544,plain,
% 1.44/1.04      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.44/1.04      | ~ r3_waybel_9(X0,X1,X2)
% 1.44/1.04      | ~ l1_waybel_0(X1,X0)
% 1.44/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.44/1.04      | ~ v7_waybel_0(X1)
% 1.44/1.04      | ~ v4_orders_2(X1)
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | v2_struct_0(X1)
% 1.44/1.04      | ~ l1_pre_topc(X0)
% 1.44/1.04      | sK1 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_545,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.44/1.04      | ~ r3_waybel_9(sK1,X0,X1)
% 1.44/1.04      | ~ l1_waybel_0(X0,sK1)
% 1.44/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.44/1.04      | ~ v7_waybel_0(X0)
% 1.44/1.04      | ~ v4_orders_2(X0)
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | v2_struct_0(sK1)
% 1.44/1.04      | ~ l1_pre_topc(sK1) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_544]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_549,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.44/1.04      | ~ r3_waybel_9(sK1,X0,X1)
% 1.44/1.04      | ~ l1_waybel_0(X0,sK1)
% 1.44/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.44/1.04      | ~ v7_waybel_0(X0)
% 1.44/1.04      | ~ v4_orders_2(X0)
% 1.44/1.04      | v2_struct_0(X0) ),
% 1.44/1.04      inference(global_propositional_subsumption,
% 1.44/1.04                [status(thm)],
% 1.44/1.04                [c_545,c_27,c_25]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_929,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ l1_waybel_0(X0,sK1)
% 1.44/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.44/1.04      | ~ v7_waybel_0(X0)
% 1.44/1.04      | ~ v4_orders_2(X0)
% 1.44/1.04      | v2_struct_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
% 1.44/1.04      | sK3 != X1
% 1.44/1.04      | sK1 != sK1 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_214,c_549]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_930,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 1.44/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_929]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_932,plain,
% 1.44/1.04      ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_930,c_19]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_933,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_932]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1043,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(X2)
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(X2)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
% 1.44/1.04      | sK1 != X2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_933]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1044,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(sK1)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | ~ l1_struct_0(sK1)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1043]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1048,plain,
% 1.44/1.04      ( v1_xboole_0(X0)
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 1.44/1.04      inference(global_propositional_subsumption,
% 1.44/1.04                [status(thm)],
% 1.44/1.04                [c_1044,c_27,c_25,c_68]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1049,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1048]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1544,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.44/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X1)
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.44/1.04      | sK2 != X0 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_1049,c_21]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1545,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | v1_xboole_0(sK2)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_1544]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1549,plain,
% 1.44/1.04      ( v1_xboole_0(X0)
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1545,c_24]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1550,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_1549]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_1976,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v1_xboole_0(X0)
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_1550]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2613,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.44/1.04      | k2_struct_0(sK1) != X0
% 1.44/1.04      | sK2 != sK2 ),
% 1.44/1.04      inference(resolution_lifted,[status(thm)],[c_1976,c_1107]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2614,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(unflattening,[status(thm)],[c_2613]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2616,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(global_propositional_subsumption,
% 1.44/1.04                [status(thm)],
% 1.44/1.04                [c_2614,c_20,c_2582,c_2599]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_2617,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.44/1.04      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 1.44/1.04      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_2616]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3313,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.44/1.04      inference(equality_resolution_simp,[status(thm)],[c_2617]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3315,plain,
% 1.44/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) ),
% 1.44/1.04      inference(global_propositional_subsumption,[status(thm)],[c_3313,c_3305]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3316,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.44/1.04      inference(renaming,[status(thm)],[c_3315]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_3752,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3)
% 1.44/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.44/1.04      inference(subtyping,[status(esa)],[c_3316]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4141,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) = iProver_top
% 1.44/1.04      | r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 1.44/1.04      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.44/1.04      inference(predicate_to_equality,[status(thm)],[c_3752]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4173,plain,
% 1.44/1.04      ( r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 1.44/1.04      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.44/1.04      inference(light_normalisation,[status(thm)],[c_4141,c_3751,c_3756]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4181,plain,
% 1.44/1.04      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.44/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_4178,c_4173]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4331,plain,
% 1.44/1.04      ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top ),
% 1.44/1.04      inference(superposition,[status(thm)],[c_4134,c_4181]) ).
% 1.44/1.04  
% 1.44/1.04  cnf(c_4475,plain,
% 1.44/1.04      ( $false ),
% 1.44/1.04      inference(superposition,[status(thm)],[c_4438,c_4331]) ).
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.44/1.04  
% 1.44/1.04  ------                               Statistics
% 1.44/1.04  
% 1.44/1.04  ------ General
% 1.44/1.04  
% 1.44/1.04  abstr_ref_over_cycles:                  0
% 1.44/1.04  abstr_ref_under_cycles:                 0
% 1.44/1.04  gc_basic_clause_elim:                   0
% 1.44/1.04  forced_gc_time:                         0
% 1.44/1.04  parsing_time:                           0.008
% 1.44/1.04  unif_index_cands_time:                  0.
% 1.44/1.04  unif_index_add_time:                    0.
% 1.44/1.04  orderings_time:                         0.
% 1.44/1.04  out_proof_time:                         0.016
% 1.44/1.04  total_time:                             0.143
% 1.44/1.04  num_of_symbols:                         60
% 1.44/1.04  num_of_terms:                           2071
% 1.44/1.04  
% 1.44/1.04  ------ Preprocessing
% 1.44/1.04  
% 1.44/1.04  num_of_splits:                          0
% 1.44/1.04  num_of_split_atoms:                     0
% 1.44/1.04  num_of_reused_defs:                     0
% 1.44/1.04  num_eq_ax_congr_red:                    23
% 1.44/1.04  num_of_sem_filtered_clauses:            1
% 1.44/1.04  num_of_subtypes:                        5
% 1.44/1.04  monotx_restored_types:                  0
% 1.44/1.04  sat_num_of_epr_types:                   0
% 1.44/1.04  sat_num_of_non_cyclic_types:            0
% 1.44/1.04  sat_guarded_non_collapsed_types:        0
% 1.44/1.04  num_pure_diseq_elim:                    0
% 1.44/1.04  simp_replaced_by:                       0
% 1.44/1.04  res_preprocessed:                       117
% 1.44/1.04  prep_upred:                             0
% 1.44/1.04  prep_unflattend:                        57
% 1.44/1.04  smt_new_axioms:                         0
% 1.44/1.04  pred_elim_cands:                        4
% 1.44/1.04  pred_elim:                              12
% 1.44/1.04  pred_elim_cl:                           13
% 1.44/1.04  pred_elim_cycles:                       28
% 1.44/1.04  merged_defs:                            12
% 1.44/1.04  merged_defs_ncl:                        0
% 1.44/1.04  bin_hyper_res:                          12
% 1.44/1.04  prep_cycles:                            5
% 1.44/1.04  pred_elim_time:                         0.058
% 1.44/1.04  splitting_time:                         0.
% 1.44/1.04  sem_filter_time:                        0.
% 1.44/1.04  monotx_time:                            0.
% 1.44/1.04  subtype_inf_time:                       0.
% 1.44/1.04  
% 1.44/1.04  ------ Problem properties
% 1.44/1.04  
% 1.44/1.04  clauses:                                13
% 1.44/1.04  conjectures:                            2
% 1.44/1.04  epr:                                    1
% 1.44/1.04  horn:                                   10
% 1.44/1.04  ground:                                 8
% 1.44/1.04  unary:                                  4
% 1.44/1.04  binary:                                 4
% 1.44/1.04  lits:                                   35
% 1.44/1.04  lits_eq:                                8
% 1.44/1.04  fd_pure:                                0
% 1.44/1.04  fd_pseudo:                              0
% 1.44/1.04  fd_cond:                                0
% 1.44/1.04  fd_pseudo_cond:                         0
% 1.44/1.04  ac_symbols:                             0
% 1.44/1.04  
% 1.44/1.04  ------ Propositional Solver
% 1.44/1.04  
% 1.44/1.04  prop_solver_calls:                      29
% 1.44/1.04  prop_fast_solver_calls:                 1721
% 1.44/1.04  smt_solver_calls:                       0
% 1.44/1.04  smt_fast_solver_calls:                  0
% 1.44/1.04  prop_num_of_clauses:                    614
% 1.44/1.04  prop_preprocess_simplified:             3033
% 1.44/1.04  prop_fo_subsumed:                       48
% 1.44/1.04  prop_solver_time:                       0.
% 1.44/1.04  smt_solver_time:                        0.
% 1.44/1.04  smt_fast_solver_time:                   0.
% 1.44/1.04  prop_fast_solver_time:                  0.
% 1.44/1.04  prop_unsat_core_time:                   0.
% 1.44/1.04  
% 1.44/1.04  ------ QBF
% 1.44/1.04  
% 1.44/1.04  qbf_q_res:                              0
% 1.44/1.04  qbf_num_tautologies:                    0
% 1.44/1.04  qbf_prep_cycles:                        0
% 1.44/1.04  
% 1.44/1.04  ------ BMC1
% 1.44/1.04  
% 1.44/1.04  bmc1_current_bound:                     -1
% 1.44/1.04  bmc1_last_solved_bound:                 -1
% 1.44/1.04  bmc1_unsat_core_size:                   -1
% 1.44/1.04  bmc1_unsat_core_parents_size:           -1
% 1.44/1.04  bmc1_merge_next_fun:                    0
% 1.44/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.44/1.04  
% 1.44/1.04  ------ Instantiation
% 1.44/1.04  
% 1.44/1.04  inst_num_of_clauses:                    86
% 1.44/1.04  inst_num_in_passive:                    2
% 1.44/1.04  inst_num_in_active:                     62
% 1.44/1.04  inst_num_in_unprocessed:                22
% 1.44/1.04  inst_num_of_loops:                      70
% 1.44/1.04  inst_num_of_learning_restarts:          0
% 1.44/1.04  inst_num_moves_active_passive:          6
% 1.44/1.04  inst_lit_activity:                      0
% 1.44/1.04  inst_lit_activity_moves:                0
% 1.44/1.04  inst_num_tautologies:                   0
% 1.44/1.04  inst_num_prop_implied:                  0
% 1.44/1.04  inst_num_existing_simplified:           0
% 1.44/1.04  inst_num_eq_res_simplified:             0
% 1.44/1.04  inst_num_child_elim:                    0
% 1.44/1.04  inst_num_of_dismatching_blockings:      8
% 1.44/1.04  inst_num_of_non_proper_insts:           45
% 1.44/1.04  inst_num_of_duplicates:                 0
% 1.44/1.04  inst_inst_num_from_inst_to_res:         0
% 1.44/1.04  inst_dismatching_checking_time:         0.
% 1.44/1.04  
% 1.44/1.04  ------ Resolution
% 1.44/1.04  
% 1.44/1.04  res_num_of_clauses:                     0
% 1.44/1.04  res_num_in_passive:                     0
% 1.44/1.04  res_num_in_active:                      0
% 1.44/1.04  res_num_of_loops:                       122
% 1.44/1.04  res_forward_subset_subsumed:            6
% 1.44/1.04  res_backward_subset_subsumed:           0
% 1.44/1.04  res_forward_subsumed:                   2
% 1.44/1.04  res_backward_subsumed:                  6
% 1.44/1.04  res_forward_subsumption_resolution:     2
% 1.44/1.04  res_backward_subsumption_resolution:    0
% 1.44/1.04  res_clause_to_clause_subsumption:       229
% 1.44/1.04  res_orphan_elimination:                 0
% 1.44/1.04  res_tautology_del:                      40
% 1.44/1.04  res_num_eq_res_simplified:              4
% 1.44/1.04  res_num_sel_changes:                    0
% 1.44/1.04  res_moves_from_active_to_pass:          0
% 1.44/1.04  
% 1.44/1.04  ------ Superposition
% 1.44/1.04  
% 1.44/1.04  sup_time_total:                         0.
% 1.44/1.04  sup_time_generating:                    0.
% 1.44/1.04  sup_time_sim_full:                      0.
% 1.44/1.04  sup_time_sim_immed:                     0.
% 1.44/1.04  
% 1.44/1.04  sup_num_of_clauses:                     14
% 1.44/1.04  sup_num_in_active:                      13
% 1.44/1.04  sup_num_in_passive:                     1
% 1.44/1.04  sup_num_of_loops:                       12
% 1.44/1.04  sup_fw_superposition:                   3
% 1.44/1.04  sup_bw_superposition:                   2
% 1.44/1.04  sup_immediate_simplified:               0
% 1.44/1.04  sup_given_eliminated:                   0
% 1.44/1.04  comparisons_done:                       0
% 1.44/1.04  comparisons_avoided:                    0
% 1.44/1.04  
% 1.44/1.04  ------ Simplifications
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  sim_fw_subset_subsumed:                 0
% 1.44/1.04  sim_bw_subset_subsumed:                 0
% 1.44/1.04  sim_fw_subsumed:                        0
% 1.44/1.04  sim_bw_subsumed:                        2
% 1.44/1.04  sim_fw_subsumption_res:                 2
% 1.44/1.04  sim_bw_subsumption_res:                 0
% 1.44/1.04  sim_tautology_del:                      1
% 1.44/1.04  sim_eq_tautology_del:                   0
% 1.44/1.04  sim_eq_res_simp:                        0
% 1.44/1.04  sim_fw_demodulated:                     0
% 1.44/1.04  sim_bw_demodulated:                     0
% 1.44/1.04  sim_light_normalised:                   5
% 1.44/1.04  sim_joinable_taut:                      0
% 1.44/1.04  sim_joinable_simp:                      0
% 1.44/1.04  sim_ac_normalised:                      0
% 1.44/1.04  sim_smt_subsumption:                    0
% 1.44/1.04  
%------------------------------------------------------------------------------
