%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:24 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 249 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  259 ( 924 expanded)
%              Number of equality atoms :   21 (  68 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f42])).

fof(f42,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28,f27])).

fof(f27,plain,
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

fof(f28,plain,
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

fof(f199,plain,(
    m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(subsumption_resolution,[],[f197,f88])).

fof(f88,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f84,f77])).

fof(f77,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(condensation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X1,X1) ) ),
    inference(resolution,[],[f73,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f69,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
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

fof(f68,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f51,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f44,f43])).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f51,plain,(
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

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),X1)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f53,f69])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | r1_tarski(sK1,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f83,f59])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(sK1,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f82,f50])).

fof(f82,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))
    | r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f67,f60])).

fof(f67,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f51,f64])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f41,f63])).

fof(f63,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f45,f62])).

fof(f62,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f197,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(resolution,[],[f193,f64])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k2_struct_0(sK0))
      | m2_connsp_2(k2_struct_0(sK0),sK0,X0) ) ),
    inference(forward_demodulation,[],[f191,f97])).

fof(f97,plain,(
    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f96,f40])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f47,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
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

fof(f191,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0)))
      | m2_connsp_2(k2_struct_0(sK0),sK0,X0) ) ),
    inference(resolution,[],[f127,f61])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(forward_demodulation,[],[f126,f63])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(forward_demodulation,[],[f125,f63])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f124,f40])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:11:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (32547)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (32531)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (32538)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (32530)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.56  % (32532)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.56  % (32531)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f200,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(subsumption_resolution,[],[f199,f42])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28,f27])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f16,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.51/0.56    inference(flattening,[],[f15])).
% 1.51/0.56  fof(f15,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f14])).
% 1.51/0.56  fof(f14,plain,(
% 1.51/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.51/0.56    inference(pure_predicate_removal,[],[f12])).
% 1.51/0.56  fof(f12,negated_conjecture,(
% 1.51/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.51/0.56    inference(negated_conjecture,[],[f11])).
% 1.51/0.56  fof(f11,conjecture,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 1.51/0.56  fof(f199,plain,(
% 1.51/0.56    m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.51/0.56    inference(subsumption_resolution,[],[f197,f88])).
% 1.51/0.56  fof(f88,plain,(
% 1.51/0.56    r1_tarski(sK1,k2_struct_0(sK0))),
% 1.51/0.56    inference(resolution,[],[f84,f77])).
% 1.51/0.56  fof(f77,plain,(
% 1.51/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.51/0.56    inference(condensation,[],[f75])).
% 1.51/0.56  fof(f75,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(X0,X0) | r1_tarski(X1,X1)) )),
% 1.51/0.56    inference(resolution,[],[f73,f70])).
% 1.51/0.56  fof(f70,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(X0,X0)) )),
% 1.51/0.56    inference(resolution,[],[f69,f59])).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.51/0.56    inference(equality_resolution,[],[f56])).
% 1.51/0.56  fof(f56,plain,(
% 1.51/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f38])).
% 1.51/0.56  fof(f38,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(rectify,[],[f35])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(nnf_transformation,[],[f3])).
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.51/0.56  fof(f69,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | r1_tarski(X0,X0)) )),
% 1.51/0.56    inference(resolution,[],[f68,f50])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,plain,(
% 1.51/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.51/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.51/0.56  fof(f68,plain,(
% 1.51/0.56    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | r1_tarski(X0,X0)) )),
% 1.51/0.56    inference(resolution,[],[f66,f60])).
% 1.51/0.56  fof(f60,plain,(
% 1.51/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.51/0.56    inference(equality_resolution,[],[f55])).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f38])).
% 1.51/0.56  fof(f66,plain,(
% 1.51/0.56    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(resolution,[],[f51,f61])).
% 1.51/0.56  fof(f61,plain,(
% 1.51/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(forward_demodulation,[],[f44,f43])).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f4])).
% 1.51/0.56  fof(f4,axiom,(
% 1.51/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.51/0.56  fof(f44,plain,(
% 1.51/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.51/0.56    inference(flattening,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.51/0.56  fof(f73,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),X1) | r1_tarski(X0,X0)) )),
% 1.51/0.56    inference(resolution,[],[f53,f69])).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f34])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.56    inference(rectify,[],[f31])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.56    inference(nnf_transformation,[],[f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.56  fof(f84,plain,(
% 1.51/0.56    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | r1_tarski(sK1,k2_struct_0(sK0))) )),
% 1.51/0.56    inference(resolution,[],[f83,f59])).
% 1.51/0.56  fof(f83,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(sK1,k2_struct_0(sK0))) )),
% 1.51/0.56    inference(resolution,[],[f82,f50])).
% 1.51/0.56  fof(f82,plain,(
% 1.51/0.56    v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(sK1,k2_struct_0(sK0))),
% 1.51/0.56    inference(resolution,[],[f67,f60])).
% 1.51/0.56  fof(f67,plain,(
% 1.51/0.56    r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.51/0.56    inference(resolution,[],[f51,f64])).
% 1.51/0.56  fof(f64,plain,(
% 1.51/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.51/0.56    inference(backward_demodulation,[],[f41,f63])).
% 1.51/0.56  fof(f63,plain,(
% 1.51/0.56    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.51/0.56    inference(resolution,[],[f45,f62])).
% 1.51/0.56  fof(f62,plain,(
% 1.51/0.56    l1_struct_0(sK0)),
% 1.51/0.56    inference(resolution,[],[f46,f40])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    l1_pre_topc(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f18])).
% 1.51/0.56  fof(f18,plain,(
% 1.51/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.51/0.56  fof(f45,plain,(
% 1.51/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f17])).
% 1.51/0.56  fof(f17,plain,(
% 1.51/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f197,plain,(
% 1.51/0.56    ~r1_tarski(sK1,k2_struct_0(sK0)) | m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.51/0.56    inference(resolution,[],[f193,f64])).
% 1.51/0.56  fof(f193,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k2_struct_0(sK0)) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) )),
% 1.51/0.56    inference(forward_demodulation,[],[f191,f97])).
% 1.51/0.56  fof(f97,plain,(
% 1.51/0.56    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.51/0.56    inference(subsumption_resolution,[],[f96,f40])).
% 1.51/0.56  fof(f96,plain,(
% 1.51/0.56    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.51/0.56    inference(resolution,[],[f47,f39])).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    v2_pre_topc(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f47,plain,(
% 1.51/0.56    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.56    inference(flattening,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 1.51/0.56  fof(f191,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) )),
% 1.51/0.56    inference(resolution,[],[f127,f61])).
% 1.51/0.56  fof(f127,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) )),
% 1.51/0.56    inference(forward_demodulation,[],[f126,f63])).
% 1.51/0.56  fof(f126,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0)) )),
% 1.51/0.56    inference(forward_demodulation,[],[f125,f63])).
% 1.51/0.56  fof(f125,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f124,f40])).
% 1.51/0.56  fof(f124,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m2_connsp_2(X1,sK0,X0)) )),
% 1.51/0.56    inference(resolution,[],[f49,f39])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f30])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.56    inference(nnf_transformation,[],[f22])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.56    inference(flattening,[],[f21])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (32531)------------------------------
% 1.51/0.56  % (32531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (32531)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (32531)Memory used [KB]: 6396
% 1.51/0.56  % (32531)Time elapsed: 0.121 s
% 1.51/0.56  % (32531)------------------------------
% 1.51/0.56  % (32531)------------------------------
% 1.51/0.56  % (32523)Success in time 0.195 s
%------------------------------------------------------------------------------
