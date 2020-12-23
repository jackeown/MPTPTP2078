%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:35 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 783 expanded)
%              Number of leaves         :   13 ( 231 expanded)
%              Depth                    :   26
%              Number of atoms          :  424 (5148 expanded)
%              Number of equality atoms :   43 ( 475 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3535,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3534,f3521])).

fof(f3521,plain,(
    ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f3512,f120])).

fof(f120,plain,(
    ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f119,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK2,sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X2,X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X2,sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v2_tops_2(X2,sK0)
            & v2_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v2_tops_2(X2,sK0)
          & v2_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(X2,sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK2,sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & v2_tops_2(X1,X0) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & v2_tops_2(X1,X0) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tops_2)).

fof(f119,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f118,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f118,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f36,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f36,plain,(
    ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f3512,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    inference(resolution,[],[f3479,f178])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_2(X0,sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f177,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK2)
      | v2_tops_2(X0,sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK2)
      | v2_tops_2(X0,sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_2(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f160,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f160,plain,(
    ! [X0] :
      ( v4_pre_topc(sK3(sK0,X0),sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK2)
      | v2_tops_2(X0,sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f158,f31])).

fof(f158,plain,(
    ! [X0] :
      ( v4_pre_topc(sK3(sK0,X0),sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK2)
      | ~ l1_pre_topc(sK0)
      | v2_tops_2(X0,sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f156,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK3(X1,X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | v2_tops_2(X0,X1)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f133,f45])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | v2_tops_2(X0,X1)
      | ~ l1_pre_topc(X1)
      | r1_tarski(sK3(X1,X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f156,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,u1_struct_0(sK0))
      | v4_pre_topc(X1,sK0)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f148,f45])).

fof(f148,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK2)
      | v4_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f147,f31])).

fof(f147,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f35])).

fof(f35,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f143,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_2(sK2,sK0)
      | v4_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | v4_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3479,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f41,f3467])).

fof(f3467,plain,(
    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f3438,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f3438,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f56,f3370])).

fof(f3370,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f3369,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3369,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f3368,f42])).

fof(f3368,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f3330,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f164,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3330,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f3318,f127])).

fof(f127,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK4(X8,X9,k1_zfmisc_1(u1_struct_0(sK0))),sK2)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(X8,X9)
      | ~ r2_hidden(sK4(X8,X9,k1_zfmisc_1(u1_struct_0(sK0))),X8) ) ),
    inference(resolution,[],[f51,f94])).

fof(f94,plain,(
    ! [X7] :
      ( r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,sK2) ) ),
    inference(resolution,[],[f72,f61])).

fof(f61,plain,(
    r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f44,f33])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(superposition,[],[f54,f43])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3318,plain,(
    ! [X20] :
      ( r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X20)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(X20,sK1)) ) ),
    inference(forward_demodulation,[],[f3317,f42])).

fof(f3317,plain,(
    ! [X20] :
      ( r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X20)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3299,f168])).

fof(f3299,plain,(
    ! [X20] :
      ( r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X20)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(X20,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f3243])).

fof(f3243,plain,(
    ! [X20] :
      ( r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X20)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(X20,sK1)) ) ),
    inference(resolution,[],[f194,f128])).

fof(f128,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,k1_zfmisc_1(u1_struct_0(sK0))),sK1)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(X10,X11)
      | ~ r2_hidden(sK4(X10,X11,k1_zfmisc_1(u1_struct_0(sK0))),X10) ) ),
    inference(resolution,[],[f51,f93])).

fof(f93,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f72,f60])).

fof(f60,plain,(
    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f44,f32])).

fof(f194,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X3)
      | r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X2)
      | k2_xboole_0(k2_xboole_0(X2,X3),X4) = X4 ) ),
    inference(resolution,[],[f168,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3534,plain,(
    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f3531,f3522])).

fof(f3522,plain,(
    ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f3513,f120])).

fof(f3513,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    inference(resolution,[],[f3479,f172])).

fof(f172,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_2(X0,sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f171,f31])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK1)
      | v2_tops_2(X0,sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK1)
      | v2_tops_2(X0,sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_2(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f154,f117])).

fof(f154,plain,(
    ! [X0] :
      ( v4_pre_topc(sK3(sK0,X0),sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK1)
      | v2_tops_2(X0,sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f152,f31])).

fof(f152,plain,(
    ! [X0] :
      ( v4_pre_topc(sK3(sK0,X0),sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK1)
      | ~ l1_pre_topc(sK0)
      | v2_tops_2(X0,sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f150,f136])).

fof(f150,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,u1_struct_0(sK0))
      | v4_pre_topc(X1,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f146,f45])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f145,f31])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f34])).

fof(f34,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f142,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_2(sK1,sK0)
      | v4_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f37,f32])).

fof(f3531,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    inference(resolution,[],[f3526,f55])).

fof(f3526,plain,(
    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f3525,f31])).

fof(f3525,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f3516,f120])).

fof(f3516,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f3479,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(resolution,[],[f39,f45])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:20:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (2029)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (2031)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (2030)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (2025)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (2025)Refutation not found, incomplete strategy% (2025)------------------------------
% 0.22/0.51  % (2025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2025)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (2025)Memory used [KB]: 6140
% 0.22/0.51  % (2025)Time elapsed: 0.085 s
% 0.22/0.51  % (2025)------------------------------
% 0.22/0.51  % (2025)------------------------------
% 0.22/0.51  % (2044)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (2045)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (2039)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (2032)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (2038)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (2033)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (2036)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (2037)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (2036)Refutation not found, incomplete strategy% (2036)------------------------------
% 0.22/0.53  % (2036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2036)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2036)Memory used [KB]: 10618
% 0.22/0.53  % (2036)Time elapsed: 0.094 s
% 0.22/0.53  % (2036)------------------------------
% 0.22/0.53  % (2036)------------------------------
% 0.22/0.53  % (2028)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (2027)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.53  % (2040)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (2045)Refutation not found, incomplete strategy% (2045)------------------------------
% 0.22/0.53  % (2045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2045)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2045)Memory used [KB]: 10618
% 0.22/0.53  % (2045)Time elapsed: 0.052 s
% 0.22/0.53  % (2045)------------------------------
% 0.22/0.53  % (2045)------------------------------
% 0.22/0.54  % (2041)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.54  % (2026)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (2026)Refutation not found, incomplete strategy% (2026)------------------------------
% 0.22/0.54  % (2026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2026)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2026)Memory used [KB]: 10618
% 0.22/0.54  % (2026)Time elapsed: 0.114 s
% 0.22/0.54  % (2026)------------------------------
% 0.22/0.54  % (2026)------------------------------
% 0.22/0.55  % (2034)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.55  % (2040)Refutation not found, incomplete strategy% (2040)------------------------------
% 0.22/0.55  % (2040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2040)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2040)Memory used [KB]: 6140
% 0.22/0.55  % (2040)Time elapsed: 0.105 s
% 0.22/0.55  % (2040)------------------------------
% 0.22/0.55  % (2040)------------------------------
% 0.22/0.56  % (2042)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.57  % (2043)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.67/0.58  % (2035)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.67/0.60  % (2035)Refutation not found, incomplete strategy% (2035)------------------------------
% 1.67/0.60  % (2035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.60  % (2035)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.60  
% 1.88/0.60  % (2035)Memory used [KB]: 6140
% 1.88/0.60  % (2035)Time elapsed: 0.161 s
% 1.88/0.60  % (2035)------------------------------
% 1.88/0.60  % (2035)------------------------------
% 2.26/0.68  % (2043)Refutation found. Thanks to Tanya!
% 2.26/0.68  % SZS status Theorem for theBenchmark
% 2.26/0.68  % SZS output start Proof for theBenchmark
% 2.26/0.68  fof(f3535,plain,(
% 2.26/0.68    $false),
% 2.26/0.68    inference(subsumption_resolution,[],[f3534,f3521])).
% 2.26/0.68  fof(f3521,plain,(
% 2.26/0.68    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 2.26/0.68    inference(subsumption_resolution,[],[f3512,f120])).
% 2.26/0.68  fof(f120,plain,(
% 2.26/0.68    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0)),
% 2.26/0.68    inference(subsumption_resolution,[],[f119,f32])).
% 2.26/0.68  fof(f32,plain,(
% 2.26/0.68    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.26/0.68    inference(cnf_transformation,[],[f20])).
% 2.26/0.68  fof(f20,plain,(
% 2.26/0.68    ((~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 2.26/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19,f18,f17])).
% 2.26/0.68  fof(f17,plain,(
% 2.26/0.68    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X2,X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 2.26/0.68    introduced(choice_axiom,[])).
% 2.26/0.68  fof(f18,plain,(
% 2.26/0.68    ? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 2.26/0.68    introduced(choice_axiom,[])).
% 2.26/0.68  fof(f19,plain,(
% 2.26/0.68    ? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 2.26/0.68    introduced(choice_axiom,[])).
% 2.26/0.68  fof(f11,plain,(
% 2.26/0.68    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X2,X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.26/0.68    inference(flattening,[],[f10])).
% 2.26/0.68  fof(f10,plain,(
% 2.26/0.68    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v2_tops_2(X2,X0) & v2_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.26/0.68    inference(ennf_transformation,[],[f9])).
% 2.26/0.68  fof(f9,negated_conjecture,(
% 2.26/0.68    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & v2_tops_2(X1,X0)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.26/0.68    inference(negated_conjecture,[],[f8])).
% 2.26/0.68  fof(f8,conjecture,(
% 2.26/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & v2_tops_2(X1,X0)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.26/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tops_2)).
% 2.26/0.68  fof(f119,plain,(
% 2.26/0.68    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.26/0.68    inference(subsumption_resolution,[],[f118,f33])).
% 2.26/0.68  fof(f33,plain,(
% 2.26/0.68    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.26/0.68    inference(cnf_transformation,[],[f20])).
% 2.26/0.68  fof(f118,plain,(
% 2.26/0.68    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.26/0.68    inference(superposition,[],[f36,f46])).
% 2.26/0.68  fof(f46,plain,(
% 2.26/0.68    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.26/0.68    inference(cnf_transformation,[],[f16])).
% 2.26/0.68  fof(f16,plain,(
% 2.26/0.68    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.26/0.68    inference(flattening,[],[f15])).
% 2.26/0.68  fof(f15,plain,(
% 2.26/0.68    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.26/0.68    inference(ennf_transformation,[],[f5])).
% 2.26/0.68  fof(f5,axiom,(
% 2.26/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.26/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.26/0.68  fof(f36,plain,(
% 2.26/0.68    ~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 2.26/0.68    inference(cnf_transformation,[],[f20])).
% 2.26/0.68  fof(f3512,plain,(
% 2.26/0.68    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 2.26/0.68    inference(resolution,[],[f3479,f178])).
% 2.26/0.68  fof(f178,plain,(
% 2.26/0.68    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK2)) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f177,f31])).
% 2.26/0.68  fof(f31,plain,(
% 2.26/0.68    l1_pre_topc(sK0)),
% 2.26/0.68    inference(cnf_transformation,[],[f20])).
% 2.26/0.68  fof(f177,plain,(
% 2.26/0.68    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK2) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.26/0.68    inference(duplicate_literal_removal,[],[f176])).
% 2.26/0.68  fof(f176,plain,(
% 2.26/0.68    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK2) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X0,sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.26/0.68    inference(resolution,[],[f160,f117])).
% 2.26/0.68  fof(f117,plain,(
% 2.26/0.68    ( ! [X0,X1] : (~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0) | ~l1_pre_topc(X0) | ~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.26/0.68    inference(resolution,[],[f40,f45])).
% 2.26/0.68  fof(f45,plain,(
% 2.26/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f25])).
% 2.26/0.68  fof(f25,plain,(
% 2.26/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.26/0.68    inference(nnf_transformation,[],[f6])).
% 2.26/0.68  fof(f6,axiom,(
% 2.26/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.26/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.26/0.68  fof(f40,plain,(
% 2.26/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f24])).
% 2.26/0.68  fof(f24,plain,(
% 2.26/0.68    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.26/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 2.26/0.68  fof(f23,plain,(
% 2.26/0.68    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.26/0.68    introduced(choice_axiom,[])).
% 2.26/0.68  fof(f22,plain,(
% 2.26/0.68    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.26/0.68    inference(rectify,[],[f21])).
% 2.26/0.68  fof(f21,plain,(
% 2.26/0.68    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.26/0.68    inference(nnf_transformation,[],[f13])).
% 2.26/0.68  fof(f13,plain,(
% 2.26/0.68    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.26/0.68    inference(flattening,[],[f12])).
% 2.26/0.68  fof(f12,plain,(
% 2.26/0.68    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.26/0.68    inference(ennf_transformation,[],[f7])).
% 2.26/0.68  fof(f7,axiom,(
% 2.26/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 2.26/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).
% 2.26/0.68  fof(f160,plain,(
% 2.26/0.68    ( ! [X0] : (v4_pre_topc(sK3(sK0,X0),sK0) | ~r2_hidden(sK3(sK0,X0),sK2) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f158,f31])).
% 2.26/0.68  fof(f158,plain,(
% 2.26/0.68    ( ! [X0] : (v4_pre_topc(sK3(sK0,X0),sK0) | ~r2_hidden(sK3(sK0,X0),sK2) | ~l1_pre_topc(sK0) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.26/0.68    inference(resolution,[],[f156,f136])).
% 2.26/0.68  fof(f136,plain,(
% 2.26/0.68    ( ! [X0,X1] : (r1_tarski(sK3(X1,X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | v2_tops_2(X0,X1) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 2.26/0.68    inference(resolution,[],[f133,f45])).
% 2.26/0.68  fof(f133,plain,(
% 2.26/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | v2_tops_2(X0,X1) | ~l1_pre_topc(X1) | r1_tarski(sK3(X1,X0),u1_struct_0(X1))) )),
% 2.26/0.68    inference(resolution,[],[f38,f44])).
% 2.26/0.68  fof(f44,plain,(
% 2.26/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f25])).
% 2.26/0.68  fof(f38,plain,(
% 2.26/0.68    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f24])).
% 2.26/0.68  fof(f156,plain,(
% 2.26/0.68    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | v4_pre_topc(X1,sK0) | ~r2_hidden(X1,sK2)) )),
% 2.26/0.68    inference(resolution,[],[f148,f45])).
% 2.26/0.68  fof(f148,plain,(
% 2.26/0.68    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2) | v4_pre_topc(X1,sK0)) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f147,f31])).
% 2.26/0.68  fof(f147,plain,(
% 2.26/0.68    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f143,f35])).
% 2.26/0.68  fof(f35,plain,(
% 2.26/0.68    v2_tops_2(sK2,sK0)),
% 2.26/0.68    inference(cnf_transformation,[],[f20])).
% 2.26/0.68  fof(f143,plain,(
% 2.26/0.68    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(sK2,sK0) | v4_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 2.26/0.68    inference(resolution,[],[f37,f33])).
% 2.26/0.68  fof(f37,plain,(
% 2.26/0.68    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | v4_pre_topc(X3,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f24])).
% 2.26/0.68  fof(f3479,plain,(
% 2.26/0.68    r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.68    inference(superposition,[],[f41,f3467])).
% 2.26/0.68  fof(f3467,plain,(
% 2.26/0.68    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.68    inference(subsumption_resolution,[],[f3438,f43])).
% 2.26/0.68  fof(f43,plain,(
% 2.26/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f14])).
% 2.26/0.68  fof(f14,plain,(
% 2.26/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.26/0.68    inference(ennf_transformation,[],[f3])).
% 2.26/0.68  fof(f3,axiom,(
% 2.26/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.26/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.26/0.68  fof(f3438,plain,(
% 2.26/0.68    r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.68    inference(superposition,[],[f56,f3370])).
% 2.26/0.68  fof(f3370,plain,(
% 2.26/0.68    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.68    inference(forward_demodulation,[],[f3369,f42])).
% 2.26/0.68  fof(f42,plain,(
% 2.26/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f1])).
% 2.26/0.68  fof(f1,axiom,(
% 2.26/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.26/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.26/0.68  fof(f3369,plain,(
% 2.26/0.68    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.68    inference(forward_demodulation,[],[f3368,f42])).
% 2.26/0.68  fof(f3368,plain,(
% 2.26/0.68    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1)) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.68    inference(subsumption_resolution,[],[f3330,f168])).
% 2.26/0.68  fof(f168,plain,(
% 2.26/0.68    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f164,f52])).
% 2.26/0.68  fof(f52,plain,(
% 2.26/0.68    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 2.26/0.68    inference(cnf_transformation,[],[f30])).
% 2.26/0.68  fof(f30,plain,(
% 2.26/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.26/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 2.26/0.68  fof(f29,plain,(
% 2.26/0.68    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.26/0.68    introduced(choice_axiom,[])).
% 2.26/0.68  fof(f28,plain,(
% 2.26/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.26/0.68    inference(rectify,[],[f27])).
% 2.26/0.68  fof(f27,plain,(
% 2.26/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.26/0.68    inference(flattening,[],[f26])).
% 2.26/0.68  fof(f26,plain,(
% 2.26/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.26/0.68    inference(nnf_transformation,[],[f2])).
% 2.26/0.68  fof(f2,axiom,(
% 2.26/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.26/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.26/0.68  fof(f164,plain,(
% 2.26/0.68    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 2.26/0.68    inference(factoring,[],[f50])).
% 2.26/0.68  fof(f50,plain,(
% 2.26/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 2.26/0.68    inference(cnf_transformation,[],[f30])).
% 2.26/0.68  fof(f3330,plain,(
% 2.26/0.68    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1)) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(sK2,sK1))),
% 2.26/0.68    inference(resolution,[],[f3318,f127])).
% 2.26/0.68  fof(f127,plain,(
% 2.26/0.68    ( ! [X8,X9] : (~r2_hidden(sK4(X8,X9,k1_zfmisc_1(u1_struct_0(sK0))),sK2) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(X8,X9) | ~r2_hidden(sK4(X8,X9,k1_zfmisc_1(u1_struct_0(sK0))),X8)) )),
% 2.26/0.68    inference(resolution,[],[f51,f94])).
% 2.26/0.68  fof(f94,plain,(
% 2.26/0.68    ( ! [X7] : (r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X7,sK2)) )),
% 2.26/0.68    inference(resolution,[],[f72,f61])).
% 2.26/0.68  fof(f61,plain,(
% 2.26/0.68    r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.68    inference(resolution,[],[f44,f33])).
% 2.26/0.68  fof(f72,plain,(
% 2.26/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 2.26/0.68    inference(superposition,[],[f54,f43])).
% 2.26/0.68  fof(f54,plain,(
% 2.26/0.68    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 2.26/0.68    inference(equality_resolution,[],[f48])).
% 2.26/0.68  fof(f48,plain,(
% 2.26/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.26/0.68    inference(cnf_transformation,[],[f30])).
% 2.26/0.68  fof(f51,plain,(
% 2.26/0.68    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 2.26/0.68    inference(cnf_transformation,[],[f30])).
% 2.26/0.68  fof(f3318,plain,(
% 2.26/0.68    ( ! [X20] : (r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X20) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(X20,sK1))) )),
% 2.26/0.68    inference(forward_demodulation,[],[f3317,f42])).
% 2.26/0.68  fof(f3317,plain,(
% 2.26/0.68    ( ! [X20] : (r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X20) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f3299,f168])).
% 2.26/0.68  fof(f3299,plain,(
% 2.26/0.68    ( ! [X20] : (r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X20) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(X20,sK1))) )),
% 2.26/0.68    inference(duplicate_literal_removal,[],[f3243])).
% 2.26/0.68  fof(f3243,plain,(
% 2.26/0.68    ( ! [X20] : (r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X20) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(k2_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(X20,sK1))) )),
% 2.26/0.68    inference(resolution,[],[f194,f128])).
% 2.26/0.68  fof(f128,plain,(
% 2.26/0.68    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,k1_zfmisc_1(u1_struct_0(sK0))),sK1) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(X10,X11) | ~r2_hidden(sK4(X10,X11,k1_zfmisc_1(u1_struct_0(sK0))),X10)) )),
% 2.26/0.68    inference(resolution,[],[f51,f93])).
% 2.26/0.68  fof(f93,plain,(
% 2.26/0.68    ( ! [X6] : (r2_hidden(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X6,sK1)) )),
% 2.26/0.68    inference(resolution,[],[f72,f60])).
% 2.26/0.68  fof(f60,plain,(
% 2.26/0.68    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.68    inference(resolution,[],[f44,f32])).
% 2.26/0.68  fof(f194,plain,(
% 2.26/0.68    ( ! [X4,X2,X3] : (r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X3) | r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X2) | k2_xboole_0(k2_xboole_0(X2,X3),X4) = X4) )),
% 2.26/0.68    inference(resolution,[],[f168,f55])).
% 2.26/0.68  fof(f55,plain,(
% 2.26/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 2.26/0.68    inference(equality_resolution,[],[f47])).
% 2.26/0.68  fof(f47,plain,(
% 2.26/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.26/0.68    inference(cnf_transformation,[],[f30])).
% 2.26/0.68  fof(f56,plain,(
% 2.26/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.26/0.68    inference(superposition,[],[f41,f42])).
% 2.26/0.68  fof(f41,plain,(
% 2.26/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.26/0.68    inference(cnf_transformation,[],[f4])).
% 2.26/0.68  fof(f4,axiom,(
% 2.26/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.26/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.26/0.68  fof(f3534,plain,(
% 2.26/0.68    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 2.26/0.68    inference(subsumption_resolution,[],[f3531,f3522])).
% 2.26/0.68  fof(f3522,plain,(
% 2.26/0.68    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)),
% 2.26/0.68    inference(subsumption_resolution,[],[f3513,f120])).
% 2.26/0.68  fof(f3513,plain,(
% 2.26/0.68    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)),
% 2.26/0.68    inference(resolution,[],[f3479,f172])).
% 2.26/0.68  fof(f172,plain,(
% 2.26/0.68    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK1)) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f171,f31])).
% 2.26/0.68  fof(f171,plain,(
% 2.26/0.68    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.26/0.68    inference(duplicate_literal_removal,[],[f170])).
% 2.26/0.68  fof(f170,plain,(
% 2.26/0.68    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X0,sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.26/0.68    inference(resolution,[],[f154,f117])).
% 2.26/0.68  fof(f154,plain,(
% 2.26/0.68    ( ! [X0] : (v4_pre_topc(sK3(sK0,X0),sK0) | ~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f152,f31])).
% 2.26/0.68  fof(f152,plain,(
% 2.26/0.68    ( ! [X0] : (v4_pre_topc(sK3(sK0,X0),sK0) | ~r2_hidden(sK3(sK0,X0),sK1) | ~l1_pre_topc(sK0) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.26/0.68    inference(resolution,[],[f150,f136])).
% 2.26/0.68  fof(f150,plain,(
% 2.26/0.68    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | v4_pre_topc(X1,sK0) | ~r2_hidden(X1,sK1)) )),
% 2.26/0.68    inference(resolution,[],[f146,f45])).
% 2.26/0.68  fof(f146,plain,(
% 2.26/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1) | v4_pre_topc(X0,sK0)) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f145,f31])).
% 2.26/0.68  fof(f145,plain,(
% 2.26/0.68    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f142,f34])).
% 2.26/0.68  fof(f34,plain,(
% 2.26/0.68    v2_tops_2(sK1,sK0)),
% 2.26/0.68    inference(cnf_transformation,[],[f20])).
% 2.26/0.68  fof(f142,plain,(
% 2.26/0.68    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(sK1,sK0) | v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 2.26/0.68    inference(resolution,[],[f37,f32])).
% 2.26/0.68  fof(f3531,plain,(
% 2.26/0.68    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 2.26/0.68    inference(resolution,[],[f3526,f55])).
% 2.26/0.68  fof(f3526,plain,(
% 2.26/0.68    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 2.26/0.68    inference(subsumption_resolution,[],[f3525,f31])).
% 2.26/0.68  fof(f3525,plain,(
% 2.26/0.68    ~l1_pre_topc(sK0) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 2.26/0.68    inference(subsumption_resolution,[],[f3516,f120])).
% 2.26/0.68  fof(f3516,plain,(
% 2.26/0.68    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~l1_pre_topc(sK0) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 2.26/0.68    inference(resolution,[],[f3479,f111])).
% 2.26/0.68  fof(f111,plain,(
% 2.26/0.68    ( ! [X0,X1] : (~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~l1_pre_topc(X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 2.26/0.68    inference(resolution,[],[f39,f45])).
% 2.26/0.68  fof(f39,plain,(
% 2.26/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),X1) | v2_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f24])).
% 2.26/0.68  % SZS output end Proof for theBenchmark
% 2.26/0.68  % (2043)------------------------------
% 2.26/0.68  % (2043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.68  % (2043)Termination reason: Refutation
% 2.26/0.68  
% 2.26/0.68  % (2043)Memory used [KB]: 3454
% 2.26/0.68  % (2043)Time elapsed: 0.260 s
% 2.26/0.68  % (2043)------------------------------
% 2.26/0.68  % (2043)------------------------------
% 2.26/0.69  % (2024)Success in time 0.318 s
%------------------------------------------------------------------------------
