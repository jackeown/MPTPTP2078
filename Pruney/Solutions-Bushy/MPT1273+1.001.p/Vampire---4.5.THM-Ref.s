%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1273+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  61 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 252 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(global_subsumption,[],[f24,f25])).

fof(f25,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f14,f17,f15,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ v2_tops_1(sK1,sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tops_1(X1,X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tops_1(X1,sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ~ v2_tops_1(X1,sK0)
        & v3_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tops_1(sK1,sK0)
      & v3_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v2_tops_1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f17,plain,(
    ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f23,f14])).

fof(f23,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f22,f15])).

fof(f22,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f18,f16])).

fof(f16,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

%------------------------------------------------------------------------------
