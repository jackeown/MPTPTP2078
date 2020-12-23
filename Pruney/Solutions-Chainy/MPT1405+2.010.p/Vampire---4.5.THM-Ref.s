%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 188 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  218 ( 691 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f38,f90,f52])).

fof(f52,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f90,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f87,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f87,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f85,f71])).

fof(f71,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f67,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f63])).

fof(f63,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f61,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f67,f37,f76])).

fof(f76,plain,(
    ! [X0] :
      ( m2_connsp_2(k2_struct_0(sK0),sK0,X0)
      | ~ r1_tarski(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f75,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

% (10079)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m2_connsp_2(k2_subset_1(k2_struct_0(sK0)),sK0,X0) ) ),
    inference(forward_demodulation,[],[f74,f59])).

fof(f59,plain,(
    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f56,f35])).

fof(f56,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m2_connsp_2(k2_subset_1(k2_struct_0(sK0)),sK0,X0) ) ),
    inference(forward_demodulation,[],[f72,f39])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k1_tops_1(sK0,k2_subset_1(k2_struct_0(sK0))))
      | m2_connsp_2(k2_subset_1(k2_struct_0(sK0)),sK0,X0) ) ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f68,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X2,k1_tops_1(sK0,X3))
      | m2_connsp_2(X3,sK0,X2) ) ),
    inference(forward_demodulation,[],[f65,f63])).

fof(f65,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X2,k1_tops_1(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | m2_connsp_2(X3,sK0,X2) ) ),
    inference(backward_demodulation,[],[f58,f63])).

fof(f58,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_tops_1(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m2_connsp_2(X3,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_tops_1(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m2_connsp_2(X3,sK0,X2) ) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f37,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (10071)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (10083)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (10074)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (10083)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (10072)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f38,f90,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.47    inference(rectify,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f87,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f85,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    r1_tarski(sK1,k2_struct_0(sK0)) | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.47    inference(resolution,[],[f70,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.47    inference(resolution,[],[f67,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.47    inference(backward_demodulation,[],[f36,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f61,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f35,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f27,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.47  fof(f12,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f11])).
% 0.21/0.47  fof(f11,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k2_struct_0(sK0))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f67,f37,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0] : (m2_connsp_2(k2_struct_0(sK0),sK0,X0) | ~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f75,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.47  % (10079)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_subset_1(k2_struct_0(sK0)),sK0,X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f74,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f35])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.47    inference(resolution,[],[f34,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_subset_1(k2_struct_0(sK0)),sK0,X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f72,f39])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,k2_subset_1(k2_struct_0(sK0)))) | m2_connsp_2(k2_subset_1(k2_struct_0(sK0)),sK0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f68,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,k1_tops_1(sK0,X3)) | m2_connsp_2(X3,sK0,X2)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f65,f63])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,k1_tops_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X3,sK0,X2)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f58,f63])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r1_tarski(X2,k1_tops_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X3,sK0,X2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f55,f35])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r1_tarski(X2,k1_tops_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m2_connsp_2(X3,sK0,X2)) )),
% 0.21/0.47    inference(resolution,[],[f34,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (10083)------------------------------
% 0.21/0.47  % (10083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (10083)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (10083)Memory used [KB]: 6140
% 0.21/0.47  % (10083)Time elapsed: 0.010 s
% 0.21/0.47  % (10083)------------------------------
% 0.21/0.47  % (10083)------------------------------
% 0.21/0.47  % (10079)Refutation not found, incomplete strategy% (10079)------------------------------
% 0.21/0.47  % (10079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (10079)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (10079)Memory used [KB]: 6140
% 0.21/0.47  % (10079)Time elapsed: 0.069 s
% 0.21/0.47  % (10079)------------------------------
% 0.21/0.47  % (10079)------------------------------
% 0.21/0.47  % (10063)Success in time 0.115 s
%------------------------------------------------------------------------------
