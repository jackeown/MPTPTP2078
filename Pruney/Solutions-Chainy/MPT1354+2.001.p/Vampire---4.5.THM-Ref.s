%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 338 expanded)
%              Number of leaves         :    9 (  94 expanded)
%              Depth                    :   30
%              Number of atoms          :  208 (1621 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(resolution,[],[f107,f89])).

fof(f89,plain,(
    ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f88,f27])).

fof(f27,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_tops_2(sK1,sK0) )
    & ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v2_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ v2_tops_2(X1,X0) )
            & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | v2_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ v2_tops_2(X1,sK0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | v2_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ v2_tops_2(X1,sK0) )
        & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | v2_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tops_2(sK1,sK0) )
      & ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).

fof(f88,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f87,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v2_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(f84,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f83,f25])).

fof(f83,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(sK1,sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f77,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f77,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f74,f24])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f72,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f72,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f71,f24])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_2(sK1,sK0)
    | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f66,f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f66,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f65,f26])).

fof(f26,plain,
    ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),X0) ) ),
    inference(forward_demodulation,[],[f62,f36])).

fof(f36,plain,(
    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),X0)
      | ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),X0)) ) ),
    inference(resolution,[],[f51,f25])).

fof(f51,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | r1_tarski(k7_setfam_1(X3,X4),X5)
      | ~ r1_tarski(k7_setfam_1(X3,k7_setfam_1(X3,X4)),k7_setfam_1(X3,X5)) ) ),
    inference(resolution,[],[f35,f34])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f107,plain,(
    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f102,f24])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f101,f28])).

fof(f101,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f99,f34])).

fof(f99,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f98,f53])).

fof(f53,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,(
    u1_pre_topc(sK0) = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f37,f24])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k7_setfam_1(u1_struct_0(X0),k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(resolution,[],[f33,f28])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f35,f25])).

fof(f98,plain,(
    r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f97,f25])).

fof(f97,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f96,f34])).

fof(f96,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f95,f24])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f93,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f92,f25])).

fof(f92,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f90,f24])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f88,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_2(X1,X0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (27323)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.49  % (27322)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.49  % (27331)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.49  % (27330)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.49  % (27323)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(resolution,[],[f107,f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.50    inference(resolution,[],[f88,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ~v2_tops_2(sK1,sK0) | ~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ((~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(sK1,sK0)) & (r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_tops_2(X1,X0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | v2_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(X1,sK0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X1] : ((~r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(X1,sK0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => ((~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(sK1,sK0)) & (r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_tops_2(X1,X0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | v2_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (((~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_tops_2(X1,X0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | v2_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((v2_tops_2(X1,X0) <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f87,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    v2_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f84,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) )),
% 0.22/0.50    inference(resolution,[],[f32,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f83,f25])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(sK1,sK0) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.50    inference(resolution,[],[f77,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f74,f24])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f72,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f71,f24])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_tops_2(sK1,sK0) | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))),
% 0.22/0.50    inference(resolution,[],[f66,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f65,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f62,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.22/0.50    inference(resolution,[],[f33,f25])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),X0) | ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),X0))) )),
% 0.22/0.50    inference(resolution,[],[f51,f25])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X3))) | r1_tarski(k7_setfam_1(X3,X4),X5) | ~r1_tarski(k7_setfam_1(X3,k7_setfam_1(X3,X4)),k7_setfam_1(X3,X5))) )),
% 0.22/0.50    inference(resolution,[],[f35,f34])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | r1_tarski(X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.50    inference(resolution,[],[f102,f24])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.50    inference(resolution,[],[f101,f28])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.50    inference(resolution,[],[f99,f34])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.50    inference(resolution,[],[f98,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.50    inference(superposition,[],[f49,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    u1_pre_topc(sK0) = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.50    inference(resolution,[],[f37,f24])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | u1_pre_topc(X0) = k7_setfam_1(u1_struct_0(X0),k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.22/0.50    inference(resolution,[],[f33,f28])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(sK1,X0)) )),
% 0.22/0.50    inference(resolution,[],[f35,f25])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))),
% 0.22/0.50    inference(resolution,[],[f97,f25])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))),
% 0.22/0.50    inference(resolution,[],[f96,f34])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))),
% 0.22/0.50    inference(resolution,[],[f95,f24])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))),
% 0.22/0.50    inference(resolution,[],[f93,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.50    inference(resolution,[],[f92,f25])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.50    inference(resolution,[],[f90,f24])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.50    inference(resolution,[],[f88,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_tops_2(X1,X0) | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (27323)------------------------------
% 0.22/0.50  % (27323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27323)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (27323)Memory used [KB]: 1663
% 0.22/0.50  % (27323)Time elapsed: 0.059 s
% 0.22/0.50  % (27323)------------------------------
% 0.22/0.50  % (27323)------------------------------
% 0.22/0.50  % (27313)Success in time 0.13 s
%------------------------------------------------------------------------------
