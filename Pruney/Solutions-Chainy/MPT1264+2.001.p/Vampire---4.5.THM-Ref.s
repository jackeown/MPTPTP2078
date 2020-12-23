%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:17 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 755 expanded)
%              Number of leaves         :   17 ( 281 expanded)
%              Depth                    :   19
%              Number of atoms          :  296 (4355 expanded)
%              Number of equality atoms :   66 ( 862 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f598,plain,(
    $false ),
    inference(subsumption_resolution,[],[f591,f83])).

fof(f83,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(forward_demodulation,[],[f82,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f82,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) ),
    inference(backward_demodulation,[],[f45,f79])).

fof(f79,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    & v3_pre_topc(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
              & v3_pre_topc(X2,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
            & v3_pre_topc(X2,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
          & v3_pre_topc(X2,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
        & v3_pre_topc(X2,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
      & v3_pre_topc(sK2,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(f45,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f591,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(backward_demodulation,[],[f104,f585])).

fof(f585,plain,(
    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f335,f335,f460,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f65,f52])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f460,plain,(
    r2_hidden(sK4(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f132,f335,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f132,plain,(
    r1_tarski(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f91,f125])).

fof(f125,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f76,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f43,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f335,plain,(
    r2_hidden(sK4(sK2,k2_struct_0(sK0),sK2),sK2) ),
    inference(subsumption_resolution,[],[f334,f83])).

fof(f334,plain,
    ( r2_hidden(sK4(sK2,k2_struct_0(sK0),sK2),sK2)
    | k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(factoring,[],[f184])).

fof(f184,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,k2_struct_0(sK0),X0),sK2)
      | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
      | r2_hidden(sK4(sK2,k2_struct_0(sK0),X0),X0) ) ),
    inference(superposition,[],[f104,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f63,f52])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f103,f51])).

fof(f103,plain,(
    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f102,f79])).

fof(f102,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f101,f77])).

fof(f77,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f40,f42,f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f42,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_pre_topc(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f100,f51])).

fof(f100,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK2))) ),
    inference(forward_demodulation,[],[f86,f93])).

fof(f93,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(forward_demodulation,[],[f89,f90])).

fof(f90,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f43,f66])).

fof(f89,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),sK2,X0) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(unit_resulting_resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f86,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f39,f40,f44,f41,f43,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

fof(f44,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:44:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (13683)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (13690)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (13690)Refutation not found, incomplete strategy% (13690)------------------------------
% 0.21/0.51  % (13690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13690)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13690)Memory used [KB]: 10746
% 0.21/0.52  % (13690)Time elapsed: 0.092 s
% 0.21/0.52  % (13690)------------------------------
% 0.21/0.52  % (13690)------------------------------
% 0.21/0.52  % (13708)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (13691)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (13691)Refutation not found, incomplete strategy% (13691)------------------------------
% 0.21/0.53  % (13691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13691)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13698)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.53  % (13687)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (13680)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.54  % (13682)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (13705)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.54  % (13681)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.54  % (13689)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (13695)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (13685)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.54  % (13684)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.54  % (13702)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.54  % (13689)Refutation not found, incomplete strategy% (13689)------------------------------
% 1.29/0.54  % (13689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (13694)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.54  % (13691)Memory used [KB]: 10746
% 1.29/0.54  % (13691)Time elapsed: 0.102 s
% 1.29/0.54  % (13691)------------------------------
% 1.29/0.54  % (13691)------------------------------
% 1.29/0.55  % (13703)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.55  % (13697)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.55  % (13709)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.55  % (13686)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.55  % (13688)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (13693)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.55  % (13697)Refutation not found, incomplete strategy% (13697)------------------------------
% 1.29/0.55  % (13697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (13701)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.55  % (13692)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.55  % (13697)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (13697)Memory used [KB]: 10618
% 1.29/0.55  % (13697)Time elapsed: 0.140 s
% 1.29/0.55  % (13697)------------------------------
% 1.29/0.55  % (13697)------------------------------
% 1.29/0.55  % (13684)Refutation not found, incomplete strategy% (13684)------------------------------
% 1.29/0.55  % (13684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (13684)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (13684)Memory used [KB]: 6268
% 1.29/0.55  % (13684)Time elapsed: 0.125 s
% 1.29/0.55  % (13684)------------------------------
% 1.29/0.55  % (13684)------------------------------
% 1.29/0.55  % (13704)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.56  % (13699)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.56  % (13707)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.56  % (13682)Refutation not found, incomplete strategy% (13682)------------------------------
% 1.29/0.56  % (13682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (13702)Refutation not found, incomplete strategy% (13702)------------------------------
% 1.50/0.56  % (13702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (13700)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.56  % (13706)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.56  % (13689)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (13689)Memory used [KB]: 10746
% 1.50/0.56  % (13689)Time elapsed: 0.127 s
% 1.50/0.56  % (13689)------------------------------
% 1.50/0.56  % (13689)------------------------------
% 1.50/0.56  % (13696)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.56  % (13702)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  % (13682)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (13682)Memory used [KB]: 10874
% 1.50/0.56  % (13682)Time elapsed: 0.120 s
% 1.50/0.56  % (13682)------------------------------
% 1.50/0.56  % (13682)------------------------------
% 1.50/0.56  % (13680)Refutation not found, incomplete strategy% (13680)------------------------------
% 1.50/0.56  % (13680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  
% 1.50/0.56  % (13702)Memory used [KB]: 10874
% 1.50/0.56  % (13702)Time elapsed: 0.086 s
% 1.50/0.56  % (13702)------------------------------
% 1.50/0.56  % (13702)------------------------------
% 1.50/0.57  % (13680)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (13680)Memory used [KB]: 1791
% 1.50/0.57  % (13680)Time elapsed: 0.135 s
% 1.50/0.57  % (13680)------------------------------
% 1.50/0.57  % (13680)------------------------------
% 1.50/0.57  % (13688)Refutation not found, incomplete strategy% (13688)------------------------------
% 1.50/0.57  % (13688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (13688)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (13688)Memory used [KB]: 10746
% 1.50/0.57  % (13688)Time elapsed: 0.139 s
% 1.50/0.57  % (13688)------------------------------
% 1.50/0.57  % (13688)------------------------------
% 1.50/0.57  % (13705)Refutation not found, incomplete strategy% (13705)------------------------------
% 1.50/0.57  % (13705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (13705)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (13705)Memory used [KB]: 6524
% 1.50/0.57  % (13705)Time elapsed: 0.160 s
% 1.50/0.57  % (13705)------------------------------
% 1.50/0.57  % (13705)------------------------------
% 1.50/0.62  % (13706)Refutation found. Thanks to Tanya!
% 1.50/0.62  % SZS status Theorem for theBenchmark
% 1.50/0.62  % SZS output start Proof for theBenchmark
% 1.50/0.62  fof(f598,plain,(
% 1.50/0.62    $false),
% 1.50/0.62    inference(subsumption_resolution,[],[f591,f83])).
% 1.50/0.62  fof(f83,plain,(
% 1.50/0.62    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 1.50/0.62    inference(forward_demodulation,[],[f82,f51])).
% 1.50/0.62  fof(f51,plain,(
% 1.50/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f3])).
% 1.50/0.62  fof(f3,axiom,(
% 1.50/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.50/0.62  fof(f82,plain,(
% 1.50/0.62    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1)))),
% 1.50/0.62    inference(backward_demodulation,[],[f45,f79])).
% 1.50/0.62  fof(f79,plain,(
% 1.50/0.62    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) )),
% 1.50/0.62    inference(unit_resulting_resolution,[],[f41,f66])).
% 1.50/0.62  fof(f66,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.50/0.62    inference(definition_unfolding,[],[f58,f52])).
% 1.50/0.62  fof(f52,plain,(
% 1.50/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.50/0.62    inference(cnf_transformation,[],[f6])).
% 1.50/0.62  fof(f6,axiom,(
% 1.50/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.50/0.62  fof(f58,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.50/0.62    inference(cnf_transformation,[],[f22])).
% 1.50/0.62  fof(f22,plain,(
% 1.50/0.62    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.50/0.62    inference(ennf_transformation,[],[f5])).
% 1.50/0.62  fof(f5,axiom,(
% 1.50/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.50/0.62  fof(f41,plain,(
% 1.50/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.62    inference(cnf_transformation,[],[f27])).
% 1.50/0.62  fof(f27,plain,(
% 1.50/0.62    ((k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.50/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).
% 1.50/0.62  fof(f24,plain,(
% 1.50/0.62    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.50/0.62    introduced(choice_axiom,[])).
% 1.50/0.62  fof(f25,plain,(
% 1.50/0.62    ? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.50/0.62    introduced(choice_axiom,[])).
% 1.50/0.62  fof(f26,plain,(
% 1.50/0.62    ? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.50/0.62    introduced(choice_axiom,[])).
% 1.50/0.62  fof(f15,plain,(
% 1.50/0.62    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.50/0.62    inference(flattening,[],[f14])).
% 1.50/0.62  fof(f14,plain,(
% 1.50/0.62    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.50/0.62    inference(ennf_transformation,[],[f13])).
% 1.50/0.62  fof(f13,negated_conjecture,(
% 1.50/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.50/0.62    inference(negated_conjecture,[],[f12])).
% 1.50/0.62  fof(f12,conjecture,(
% 1.50/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 1.50/0.62  fof(f45,plain,(
% 1.50/0.62    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 1.50/0.62    inference(cnf_transformation,[],[f27])).
% 1.50/0.62  fof(f591,plain,(
% 1.50/0.62    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 1.50/0.62    inference(backward_demodulation,[],[f104,f585])).
% 1.50/0.62  fof(f585,plain,(
% 1.50/0.62    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))),
% 1.50/0.62    inference(unit_resulting_resolution,[],[f335,f335,f460,f67])).
% 1.50/0.62  fof(f67,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.50/0.62    inference(definition_unfolding,[],[f65,f52])).
% 1.50/0.62  fof(f65,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f38])).
% 1.50/0.62  fof(f38,plain,(
% 1.50/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.50/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.50/0.62  fof(f37,plain,(
% 1.50/0.62    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.50/0.62    introduced(choice_axiom,[])).
% 1.50/0.62  fof(f36,plain,(
% 1.50/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.50/0.62    inference(rectify,[],[f35])).
% 1.50/0.62  fof(f35,plain,(
% 1.50/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.50/0.62    inference(flattening,[],[f34])).
% 1.50/0.62  fof(f34,plain,(
% 1.50/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.50/0.62    inference(nnf_transformation,[],[f2])).
% 1.50/0.62  fof(f2,axiom,(
% 1.50/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.50/0.62  fof(f460,plain,(
% 1.50/0.62    r2_hidden(sK4(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0))),
% 1.50/0.62    inference(unit_resulting_resolution,[],[f132,f335,f53])).
% 1.50/0.62  fof(f53,plain,(
% 1.50/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f32])).
% 1.50/0.62  fof(f32,plain,(
% 1.50/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.50/0.62  fof(f31,plain,(
% 1.50/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.50/0.62    introduced(choice_axiom,[])).
% 1.50/0.62  fof(f30,plain,(
% 1.50/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.62    inference(rectify,[],[f29])).
% 1.50/0.62  fof(f29,plain,(
% 1.50/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.62    inference(nnf_transformation,[],[f21])).
% 1.50/0.62  fof(f21,plain,(
% 1.50/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.62    inference(ennf_transformation,[],[f1])).
% 1.50/0.62  fof(f1,axiom,(
% 1.50/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.62  fof(f132,plain,(
% 1.50/0.62    r1_tarski(sK2,k2_struct_0(sK0))),
% 1.50/0.62    inference(backward_demodulation,[],[f91,f125])).
% 1.50/0.62  fof(f125,plain,(
% 1.50/0.62    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.50/0.62    inference(unit_resulting_resolution,[],[f76,f46])).
% 1.50/0.62  fof(f46,plain,(
% 1.50/0.62    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f16])).
% 1.50/0.62  fof(f16,plain,(
% 1.50/0.62    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.50/0.62    inference(ennf_transformation,[],[f8])).
% 1.50/0.62  fof(f8,axiom,(
% 1.50/0.62    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.50/0.62  fof(f76,plain,(
% 1.50/0.62    l1_struct_0(sK0)),
% 1.50/0.62    inference(unit_resulting_resolution,[],[f40,f47])).
% 1.50/0.62  fof(f47,plain,(
% 1.50/0.62    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f17])).
% 1.50/0.62  fof(f17,plain,(
% 1.50/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.50/0.62    inference(ennf_transformation,[],[f9])).
% 1.50/0.62  fof(f9,axiom,(
% 1.50/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.50/0.62  fof(f40,plain,(
% 1.50/0.62    l1_pre_topc(sK0)),
% 1.50/0.62    inference(cnf_transformation,[],[f27])).
% 1.50/0.62  fof(f91,plain,(
% 1.50/0.62    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.50/0.62    inference(unit_resulting_resolution,[],[f43,f56])).
% 1.50/0.62  fof(f56,plain,(
% 1.50/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.50/0.62    inference(cnf_transformation,[],[f33])).
% 1.50/0.62  fof(f33,plain,(
% 1.50/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.50/0.62    inference(nnf_transformation,[],[f7])).
% 1.50/0.62  fof(f7,axiom,(
% 1.50/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.50/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.50/0.62  fof(f43,plain,(
% 1.50/0.62    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.62    inference(cnf_transformation,[],[f27])).
% 1.50/0.62  fof(f335,plain,(
% 1.50/0.62    r2_hidden(sK4(sK2,k2_struct_0(sK0),sK2),sK2)),
% 1.50/0.62    inference(subsumption_resolution,[],[f334,f83])).
% 1.50/0.62  fof(f334,plain,(
% 1.50/0.62    r2_hidden(sK4(sK2,k2_struct_0(sK0),sK2),sK2) | k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 1.50/0.62    inference(factoring,[],[f184])).
% 1.50/0.62  fof(f184,plain,(
% 1.50/0.62    ( ! [X0] : (r2_hidden(sK4(sK2,k2_struct_0(sK0),X0),sK2) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | r2_hidden(sK4(sK2,k2_struct_0(sK0),X0),X0)) )),
% 1.50/0.62    inference(superposition,[],[f104,f69])).
% 1.50/0.62  fof(f69,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.50/0.62    inference(definition_unfolding,[],[f63,f52])).
% 1.50/0.62  fof(f63,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f38])).
% 1.50/0.62  fof(f104,plain,(
% 1.50/0.62    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))),
% 1.50/0.62    inference(forward_demodulation,[],[f103,f51])).
% 1.50/0.62  fof(f103,plain,(
% 1.50/0.62    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))),
% 1.50/0.62    inference(forward_demodulation,[],[f102,f79])).
% 1.50/0.63  fof(f102,plain,(
% 1.50/0.63    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))),
% 1.50/0.63    inference(forward_demodulation,[],[f101,f77])).
% 1.50/0.63  fof(f77,plain,(
% 1.50/0.63    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.50/0.63    inference(unit_resulting_resolution,[],[f40,f42,f41,f48])).
% 1.50/0.63  fof(f48,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f28])).
% 1.50/0.63  fof(f28,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.63    inference(nnf_transformation,[],[f18])).
% 1.50/0.63  fof(f18,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.63    inference(ennf_transformation,[],[f10])).
% 1.50/0.63  fof(f10,axiom,(
% 1.50/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 1.50/0.63  fof(f42,plain,(
% 1.50/0.63    v1_tops_1(sK1,sK0)),
% 1.50/0.63    inference(cnf_transformation,[],[f27])).
% 1.50/0.63  fof(f101,plain,(
% 1.50/0.63    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_pre_topc(sK0,sK1))))),
% 1.50/0.63    inference(forward_demodulation,[],[f100,f51])).
% 1.50/0.63  fof(f100,plain,(
% 1.50/0.63    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK2)))),
% 1.50/0.63    inference(forward_demodulation,[],[f86,f93])).
% 1.50/0.63  fof(f93,plain,(
% 1.50/0.63    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))) )),
% 1.50/0.63    inference(forward_demodulation,[],[f89,f90])).
% 1.50/0.63  fof(f90,plain,(
% 1.50/0.63    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) )),
% 1.50/0.63    inference(unit_resulting_resolution,[],[f43,f66])).
% 1.50/0.63  fof(f89,plain,(
% 1.50/0.63    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK2,X0) = k9_subset_1(u1_struct_0(sK0),X0,sK2)) )),
% 1.50/0.63    inference(unit_resulting_resolution,[],[f43,f59])).
% 1.50/0.63  fof(f59,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f23])).
% 1.50/0.63  fof(f23,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.50/0.63    inference(ennf_transformation,[],[f4])).
% 1.50/0.63  fof(f4,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.50/0.63  fof(f86,plain,(
% 1.50/0.63    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)))),
% 1.50/0.63    inference(unit_resulting_resolution,[],[f39,f40,f44,f41,f43,f50])).
% 1.50/0.63  fof(f50,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f20])).
% 1.50/0.63  fof(f20,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.63    inference(flattening,[],[f19])).
% 1.50/0.63  fof(f19,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.63    inference(ennf_transformation,[],[f11])).
% 1.50/0.63  fof(f11,axiom,(
% 1.50/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
% 1.50/0.63  fof(f44,plain,(
% 1.50/0.63    v3_pre_topc(sK2,sK0)),
% 1.50/0.63    inference(cnf_transformation,[],[f27])).
% 1.50/0.63  fof(f39,plain,(
% 1.50/0.63    v2_pre_topc(sK0)),
% 1.50/0.63    inference(cnf_transformation,[],[f27])).
% 1.50/0.63  % SZS output end Proof for theBenchmark
% 1.50/0.63  % (13706)------------------------------
% 1.50/0.63  % (13706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.63  % (13706)Termination reason: Refutation
% 1.50/0.63  
% 1.50/0.63  % (13706)Memory used [KB]: 11001
% 1.50/0.63  % (13706)Time elapsed: 0.212 s
% 1.50/0.63  % (13706)------------------------------
% 1.50/0.63  % (13706)------------------------------
% 1.50/0.63  % (13679)Success in time 0.254 s
%------------------------------------------------------------------------------
