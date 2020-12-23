%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 170 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :   21
%              Number of atoms          :  310 ( 756 expanded)
%              Number of equality atoms :   42 (  83 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(resolution,[],[f323,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f323,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f301,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f84,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f65,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f84,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f301,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f88,f296])).

fof(f296,plain,(
    sK1 = k9_setfam_1(sK0) ),
    inference(resolution,[],[f285,f90])).

fof(f90,plain,(
    r2_hidden(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f44,f89])).

fof(f89,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( v1_xboole_0(sK2)
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & v2_waybel_0(sK1,k3_yellow_1(sK0))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).

% (18977)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
          & v13_waybel_0(X1,k3_yellow_1(sK0))
          & v2_waybel_0(X1,k3_yellow_1(sK0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( v1_xboole_0(X2)
            & r2_hidden(X2,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
        & v13_waybel_0(X1,k3_yellow_1(sK0))
        & v2_waybel_0(X1,k3_yellow_1(sK0))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( v1_xboole_0(X2)
          & r2_hidden(X2,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v13_waybel_0(sK1,k3_yellow_1(sK0))
      & v2_waybel_0(sK1,k3_yellow_1(sK0))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( v1_xboole_0(X2)
        & r2_hidden(X2,sK1) )
   => ( v1_xboole_0(sK2)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f44,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f285,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | sK1 = k9_setfam_1(sK0) ),
    inference(resolution,[],[f280,f87])).

fof(f87,plain,(
    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ),
    inference(backward_demodulation,[],[f67,f58])).

fof(f58,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f67,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))) ),
    inference(definition_unfolding,[],[f43,f65,f60])).

fof(f60,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f280,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | ~ r2_hidden(k1_xboole_0,sK1)
    | sK1 = k9_setfam_1(sK0) ),
    inference(resolution,[],[f279,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f279,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(sK5(k9_setfam_1(sK0),sK1)))
      | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | sK1 = k9_setfam_1(sK0) ) ),
    inference(resolution,[],[f276,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f276,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK5(k9_setfam_1(sK0),sK1))
      | sK1 = k9_setfam_1(sK0)
      | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
      | ~ r2_hidden(X5,sK1) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK5(k9_setfam_1(sK0),sK1))
      | sK1 = k9_setfam_1(sK0)
      | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
      | ~ r2_hidden(X5,sK1)
      | sK1 = k9_setfam_1(sK0)
      | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ) ),
    inference(resolution,[],[f245,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK5(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK5(X0,sK1))
      | ~ m1_subset_1(sK5(X0,sK1),k9_setfam_1(sK0))
      | sK1 = X0
      | ~ m1_subset_1(sK1,k9_setfam_1(X0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f228,f80])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK5(X0,sK1),sK0)
      | ~ r1_tarski(X1,sK5(X0,sK1))
      | ~ r2_hidden(X1,sK1)
      | sK1 = X0
      | ~ m1_subset_1(sK1,k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f206,f87])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK5(X0,sK1),sK0)
      | ~ r1_tarski(X1,sK5(X0,sK1))
      | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
      | ~ r2_hidden(X1,sK1)
      | sK1 = X0
      | ~ m1_subset_1(sK1,k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f159,f68])).

fof(f68,plain,(
    v13_waybel_0(sK1,k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f42,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f159,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK5(X3,X0),X1)
      | ~ r1_tarski(X2,sK5(X3,X0))
      | ~ v13_waybel_0(X0,k2_yellow_1(k9_setfam_1(X1)))
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1)))
      | X0 = X3
      | ~ m1_subset_1(X0,k9_setfam_1(X3)) ) ),
    inference(resolution,[],[f155,f77])).

% (18966)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f155,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(forward_demodulation,[],[f76,f58])).

fof(f76,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) ) ),
    inference(definition_unfolding,[],[f47,f60,f65,f60])).

fof(f47,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ( ~ r2_hidden(sK4(X0,X1),X1)
            & r2_hidden(sK3(X0,X1),X1)
            & r1_tarski(sK4(X0,X1),X0)
            & r1_tarski(sK3(X0,X1),sK4(X0,X1)) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r1_tarski(X3,X0)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1)
        & r1_tarski(sK4(X0,X1),X0)
        & r1_tarski(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X2,X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ r1_tarski(X3,X0)
              | ~ r1_tarski(X2,X3) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(nnf_transformation,[],[f19])).

% (18991)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f88,plain,(
    v1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f70,f58])).

fof(f70,plain,(
    v1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f40,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:50:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (18990)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (18967)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (18974)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (18971)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (18970)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (18967)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (18990)Refutation not found, incomplete strategy% (18990)------------------------------
% 0.22/0.52  % (18990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18990)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18990)Memory used [KB]: 10746
% 0.22/0.52  % (18990)Time elapsed: 0.105 s
% 0.22/0.52  % (18990)------------------------------
% 0.22/0.52  % (18990)------------------------------
% 0.22/0.53  % (18973)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (18964)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f324,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(resolution,[],[f323,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f323,plain,(
% 0.22/0.53    ~r1_tarski(sK1,sK1)),
% 0.22/0.53    inference(resolution,[],[f301,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_subset_1(X0,X0) | ~r1_tarski(X0,X0)) )),
% 0.22/0.53    inference(resolution,[],[f84,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k9_setfam_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f55,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f56,f65])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    v1_subset_1(sK1,sK1)),
% 0.22/0.53    inference(backward_demodulation,[],[f88,f296])).
% 0.22/0.53  fof(f296,plain,(
% 0.22/0.53    sK1 = k9_setfam_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f285,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    r2_hidden(k1_xboole_0,sK1)),
% 0.22/0.53    inference(backward_demodulation,[],[f44,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    k1_xboole_0 = sK2),
% 0.22/0.53    inference(resolution,[],[f61,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    v1_xboole_0(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ((v1_xboole_0(sK2) & r2_hidden(sK2,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(sK1,k3_yellow_1(sK0)) & v2_waybel_0(sK1,k3_yellow_1(sK0)) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).
% 0.22/0.53  % (18977)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(X1,k3_yellow_1(sK0)) & v2_waybel_0(X1,k3_yellow_1(sK0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(X1,k3_yellow_1(sK0)) & v2_waybel_0(X1,k3_yellow_1(sK0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(X1)) => (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(sK1,k3_yellow_1(sK0)) & v2_waybel_0(sK1,k3_yellow_1(sK0)) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,sK1)) => (v1_xboole_0(sK2) & r2_hidden(sK2,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    r2_hidden(sK2,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    ~r2_hidden(k1_xboole_0,sK1) | sK1 = k9_setfam_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f280,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))),
% 0.22/0.53    inference(backward_demodulation,[],[f67,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))))),
% 0.22/0.53    inference(definition_unfolding,[],[f43,f65,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~r2_hidden(k1_xboole_0,sK1) | sK1 = k9_setfam_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f279,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f66,f65])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(sK5(k9_setfam_1(sK0),sK1))) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~r2_hidden(X0,sK1) | sK1 = k9_setfam_1(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f276,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k9_setfam_1(X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f54,f65])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    ( ! [X5] : (~r1_tarski(X5,sK5(k9_setfam_1(sK0),sK1)) | sK1 = k9_setfam_1(sK0) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~r2_hidden(X5,sK1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f275])).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    ( ! [X5] : (~r1_tarski(X5,sK5(k9_setfam_1(sK0),sK1)) | sK1 = k9_setfam_1(sK0) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~r2_hidden(X5,sK1) | sK1 = k9_setfam_1(sK0) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))) )),
% 0.22/0.53    inference(resolution,[],[f245,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f52,f65])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK5(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,sK5(X0,sK1)) | ~m1_subset_1(sK5(X0,sK1),k9_setfam_1(sK0)) | sK1 = X0 | ~m1_subset_1(sK1,k9_setfam_1(X0)) | ~r2_hidden(X1,sK1)) )),
% 0.22/0.53    inference(resolution,[],[f228,f80])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK5(X0,sK1),sK0) | ~r1_tarski(X1,sK5(X0,sK1)) | ~r2_hidden(X1,sK1) | sK1 = X0 | ~m1_subset_1(sK1,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(resolution,[],[f206,f87])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK5(X0,sK1),sK0) | ~r1_tarski(X1,sK5(X0,sK1)) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~r2_hidden(X1,sK1) | sK1 = X0 | ~m1_subset_1(sK1,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(resolution,[],[f159,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    v13_waybel_0(sK1,k2_yellow_1(k9_setfam_1(sK0)))),
% 0.22/0.53    inference(definition_unfolding,[],[f42,f60])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK5(X3,X0),X1) | ~r1_tarski(X2,sK5(X3,X0)) | ~v13_waybel_0(X0,k2_yellow_1(k9_setfam_1(X1))) | ~r2_hidden(X2,X0) | ~m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1))) | X0 = X3 | ~m1_subset_1(X0,k9_setfam_1(X3))) )),
% 0.22/0.53    inference(resolution,[],[f155,f77])).
% 0.22/0.53  % (18966)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f53,f65])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK5(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f76,f58])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0))) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f47,f60,f65,f60])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r1_tarski(sK4(X0,X1),X0) & r1_tarski(sK3(X0,X1),sK4(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r1_tarski(sK4(X0,X1),X0) & r1_tarski(sK3(X0,X1),sK4(X0,X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.22/0.53    inference(rectify,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  % (18991)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    v1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.22/0.53    inference(backward_demodulation,[],[f70,f58])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    v1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 0.22/0.53    inference(definition_unfolding,[],[f40,f60])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (18967)------------------------------
% 0.22/0.53  % (18967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18967)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (18967)Memory used [KB]: 1918
% 0.22/0.53  % (18967)Time elapsed: 0.105 s
% 0.22/0.53  % (18967)------------------------------
% 0.22/0.53  % (18967)------------------------------
% 0.22/0.53  % (18966)Refutation not found, incomplete strategy% (18966)------------------------------
% 0.22/0.53  % (18966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18966)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18966)Memory used [KB]: 1791
% 0.22/0.53  % (18966)Time elapsed: 0.106 s
% 0.22/0.53  % (18966)------------------------------
% 0.22/0.53  % (18966)------------------------------
% 0.22/0.53  % (18961)Success in time 0.165 s
%------------------------------------------------------------------------------
