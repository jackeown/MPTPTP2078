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
% DateTime   : Thu Dec  3 13:14:42 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  177 (3305 expanded)
%              Number of leaves         :   11 ( 797 expanded)
%              Depth                    :  111
%              Number of atoms          : 1110 (17576 expanded)
%              Number of equality atoms :    4 ( 400 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(resolution,[],[f193,f117])).

fof(f117,plain,(
    ~ v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f116,f32])).

fof(f32,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ v1_compts_1(sK0) )
    & ( v2_compts_1(k2_struct_0(sK0),sK0)
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0) )
   => ( ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
        | ~ v1_compts_1(sK0) )
      & ( v2_compts_1(k2_struct_0(sK0),sK0)
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
        | ~ v1_compts_1(X0) )
      & ( v2_compts_1(k2_struct_0(X0),X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
        | ~ v1_compts_1(X0) )
      & ( v2_compts_1(k2_struct_0(X0),X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> v2_compts_1(k2_struct_0(X0),X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v1_compts_1(X0)
        <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(f116,plain,(
    v1_compts_1(sK0) ),
    inference(resolution,[],[f115,f52])).

fof(f52,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f115,plain,
    ( ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f113,f54])).

fof(f54,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f34,f53])).

fof(f53,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f33,f52])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f113,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f112,f30])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( v1_compts_1(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f110,f56])).

fof(f56,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f40,f53])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ v1_finset_1(X2)
                | ~ m1_setfam_1(X2,u1_struct_0(X0))
                | ~ r1_tarski(X2,sK1(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & v1_tops_2(sK1(X0),X0)
            & m1_setfam_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X3] :
              ( ( v1_finset_1(sK2(X0,X3))
                & m1_setfam_1(sK2(X0,X3),u1_struct_0(X0))
                & r1_tarski(sK2(X0,X3),X3)
                & m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X3,X0)
              | ~ m1_setfam_1(X3,u1_struct_0(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f23,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v1_finset_1(X2)
              | ~ m1_setfam_1(X2,u1_struct_0(X0))
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X1,X0)
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X2] :
            ( ~ v1_finset_1(X2)
            | ~ m1_setfam_1(X2,u1_struct_0(X0))
            | ~ r1_tarski(X2,sK1(X0))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK1(X0),X0)
        & m1_setfam_1(sK1(X0),u1_struct_0(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( v1_finset_1(X4)
          & m1_setfam_1(X4,u1_struct_0(X0))
          & r1_tarski(X4,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK2(X0,X3))
        & m1_setfam_1(sK2(X0,X3),u1_struct_0(X0))
        & r1_tarski(sK2(X0,X3),X3)
        & m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ v1_finset_1(X2)
                  | ~ m1_setfam_1(X2,u1_struct_0(X0))
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X1,X0)
              & m1_setfam_1(X1,u1_struct_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v1_finset_1(X4)
                  & m1_setfam_1(X4,u1_struct_0(X0))
                  & r1_tarski(X4,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X3,X0)
              | ~ m1_setfam_1(X3,u1_struct_0(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ v1_finset_1(X2)
                  | ~ m1_setfam_1(X2,u1_struct_0(X0))
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X1,X0)
              & m1_setfam_1(X1,u1_struct_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( v1_finset_1(X2)
                  & m1_setfam_1(X2,u1_struct_0(X0))
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_setfam_1(X1,u1_struct_0(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ~ ( v1_finset_1(X2)
                        & m1_setfam_1(X2,u1_struct_0(X0))
                        & r1_tarski(X2,X1) ) )
                & v1_tops_2(X1,X0)
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_compts_1)).

fof(f110,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f109,f30])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0)
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f107,f55])).

fof(f55,plain,
    ( m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f41,f53])).

fof(f41,plain,(
    ! [X0] :
      ( m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f107,plain,
    ( ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f104,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_tops_2(sK1(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,
    ( ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f102,f31])).

fof(f31,plain,
    ( v2_compts_1(k2_struct_0(sK0),sK0)
    | v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,
    ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( v1_compts_1(sK0)
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ v1_tops_2(X1,sK0)
      | ~ m1_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f44,f53])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ( ! [X3] :
                    ( ~ v1_finset_1(X3)
                    | ~ m1_setfam_1(X3,X1)
                    | ~ r1_tarski(X3,sK3(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & v1_tops_2(sK3(X0,X1),X0)
                & m1_setfam_1(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ( v1_finset_1(sK4(X0,X1,X4))
                    & m1_setfam_1(sK4(X0,X1,X4),X1)
                    & r1_tarski(sK4(X0,X1,X4),X4)
                    & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ v1_finset_1(X3)
              | ~ m1_setfam_1(X3,X1)
              | ~ r1_tarski(X3,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X2,X0)
          & m1_setfam_1(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X3] :
            ( ~ v1_finset_1(X3)
            | ~ m1_setfam_1(X3,X1)
            | ~ r1_tarski(X3,sK3(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK3(X0,X1),X0)
        & m1_setfam_1(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( v1_finset_1(X5)
          & m1_setfam_1(X5,X1)
          & r1_tarski(X5,X4)
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK4(X0,X1,X4))
        & m1_setfam_1(sK4(X0,X1,X4),X1)
        & r1_tarski(sK4(X0,X1,X4),X4)
        & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( v1_finset_1(X5)
                      & m1_setfam_1(X5,X1)
                      & r1_tarski(X5,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( v1_finset_1(X3)
                      & m1_setfam_1(X3,X1)
                      & r1_tarski(X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X2,X0)
                  | ~ m1_setfam_1(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ~ ( v1_finset_1(X3)
                            & m1_setfam_1(X3,X1)
                            & r1_tarski(X3,X2) ) )
                    & v1_tops_2(X2,X0)
                    & m1_setfam_1(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_compts_1)).

fof(f100,plain,
    ( ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f99,f30])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_compts_1(sK0)
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f97,f55])).

fof(f97,plain,
    ( ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f94,f42])).

fof(f94,plain,
    ( ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f92,f31])).

fof(f92,plain,
    ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f91,f53])).

fof(f91,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f89,f53])).

fof(f89,plain,
    ( ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ v1_tops_2(sK1(sK0),sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f87,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( m1_setfam_1(sK4(X0,X1,X4),X1)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,
    ( ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k2_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f86,f53])).

fof(f86,plain,
    ( ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k2_struct_0(sK0))
    | v1_compts_1(sK0)
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f85,f53])).

fof(f85,plain,
    ( v1_compts_1(sK0)
    | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( v1_compts_1(sK0)
    | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK1(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_compts_1(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f83,f42])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f82,f52])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f79,f54])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ) ),
    inference(resolution,[],[f78,f30])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f71,f31])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f70,f53])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f68,f53])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v1_tops_2(sK1(X0),sK0)
      | ~ m1_setfam_1(sK1(X0),k2_struct_0(sK0))
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X4),X4)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(sK4(sK0,k2_struct_0(sK0),X3),sK1(X4))
      | ~ m1_setfam_1(X3,k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(X3,sK0)
      | v1_compts_1(X4)
      | ~ m1_setfam_1(sK4(sK0,k2_struct_0(sK0),X3),u1_struct_0(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(sK4(sK0,k2_struct_0(sK0),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ v1_finset_1(X2)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X2,sK1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0] :
      ( v1_finset_1(sK4(sK0,k2_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(X0,k2_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f62,f52])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | ~ m1_setfam_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v1_finset_1(sK4(sK0,k2_struct_0(sK0),X0))
      | v1_compts_1(sK0)
      | ~ v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f61,f54])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_2(X0,sK0)
      | ~ m1_setfam_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v1_finset_1(sK4(sK0,k2_struct_0(sK0),X0))
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f60,f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ v1_tops_2(X0,sK0)
      | ~ m1_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_finset_1(sK4(sK0,X1,X0)) ) ),
    inference(forward_demodulation,[],[f59,f53])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ v1_tops_2(X0,sK0)
      | ~ m1_setfam_1(X0,X1)
      | ~ v2_compts_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_finset_1(sK4(sK0,X1,X0)) ) ),
    inference(forward_demodulation,[],[f58,f53])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_setfam_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v2_compts_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_finset_1(sK4(sK0,X1,X0)) ) ),
    inference(resolution,[],[f47,f30])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_finset_1(sK4(X0,X1,X4)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f193,plain,(
    v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f192,f52])).

fof(f192,plain,
    ( ~ l1_struct_0(sK0)
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f191,f54])).

fof(f191,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f190,f30])).

fof(f190,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f188,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f48,f53])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f188,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f187,f30])).

fof(f187,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f185,f53])).

fof(f185,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f183,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(sK3(X0,X1),X1)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f183,plain,
    ( ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f181,f53])).

fof(f181,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f179,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_2(sK3(X0,X1),X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f179,plain,
    ( ~ v1_tops_2(sK3(sK0,k2_struct_0(sK0)),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ v1_tops_2(sK3(sK0,k2_struct_0(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f177,f127])).

fof(f127,plain,(
    ! [X1] :
      ( m1_setfam_1(sK2(sK0,X1),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(X1,k2_struct_0(sK0))
      | ~ v1_tops_2(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f126,f53])).

fof(f126,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(X1,k2_struct_0(sK0))
      | ~ v1_tops_2(X1,sK0)
      | m1_setfam_1(sK2(sK0,X1),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f125,f53])).

fof(f125,plain,(
    ! [X1] :
      ( ~ m1_setfam_1(X1,k2_struct_0(sK0))
      | ~ v1_tops_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | m1_setfam_1(sK2(sK0,X1),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f119,f53])).

fof(f119,plain,(
    ! [X1] :
      ( ~ v1_tops_2(X1,sK0)
      | ~ m1_setfam_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | m1_setfam_1(sK2(sK0,X1),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f116,f38])).

fof(f38,plain,(
    ! [X0,X3] :
      ( ~ v1_compts_1(X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_setfam_1(sK2(X0,X3),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f177,plain,
    ( ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f175,f53])).

fof(f175,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f173,f49])).

fof(f173,plain,
    ( ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f171,f142])).

fof(f142,plain,(
    ! [X0] :
      ( r1_tarski(sK2(sK0,sK3(sK0,X0)),sK3(sK0,X0))
      | ~ m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f141,f53])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0))
      | r1_tarski(sK2(sK0,sK3(sK0,X0)),sK3(sK0,X0))
      | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f139,f50])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_setfam_1(X0,k2_struct_0(sK0))
      | r1_tarski(sK2(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ) ),
    inference(resolution,[],[f129,f30])).

fof(f129,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_setfam_1(X2,k2_struct_0(sK0))
      | ~ v1_tops_2(X2,sK0)
      | r1_tarski(sK2(sK0,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f128,f53])).

fof(f128,plain,(
    ! [X2] :
      ( ~ m1_setfam_1(X2,k2_struct_0(sK0))
      | ~ v1_tops_2(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r1_tarski(sK2(sK0,X2),X2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f120,f53])).

fof(f120,plain,(
    ! [X2] :
      ( ~ v1_tops_2(X2,sK0)
      | ~ m1_setfam_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r1_tarski(sK2(sK0,X2),X2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f116,f37])).

fof(f37,plain,(
    ! [X0,X3] :
      ( ~ v1_compts_1(X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(sK2(X0,X3),X3)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | v2_compts_1(X0,sK0) ) ),
    inference(resolution,[],[f170,f52])).

fof(f170,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | v2_compts_1(X0,sK0) ) ),
    inference(resolution,[],[f169,f54])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(k2_struct_0(sK0),sK0) ) ),
    inference(resolution,[],[f168,f30])).

fof(f168,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(k2_struct_0(sK0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f166,f57])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f165,f30])).

fof(f165,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f163,f53])).

fof(f163,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ l1_pre_topc(sK0)
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f161,f49])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f160,f53])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ l1_pre_topc(sK0)
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f158,f50])).

fof(f158,plain,(
    ! [X0] :
      ( ~ v1_tops_2(sK3(sK0,k2_struct_0(sK0)),sK0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f157,f124])).

fof(f124,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(X0,k2_struct_0(sK0))
      | ~ v1_tops_2(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f123,f53])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(X0,k2_struct_0(sK0))
      | ~ v1_tops_2(X0,sK0)
      | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f122,f53])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(X0,k2_struct_0(sK0))
      | ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f118,f53])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_setfam_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f116,f36])).

fof(f36,plain,(
    ! [X0,X3] :
      ( ~ v1_compts_1(X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK0) ) ),
    inference(resolution,[],[f156,f30])).

fof(f156,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_compts_1(X0,sK0)
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ) ),
    inference(superposition,[],[f154,f53])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | v2_compts_1(X0,X1)
      | ~ m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0)
      | ~ r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(X1,X0))
      | v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f153,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_finset_1(X3)
      | v2_compts_1(X1,X0)
      | ~ m1_setfam_1(X3,X1)
      | ~ r1_tarski(X3,sK3(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f153,plain,
    ( v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f152,f52])).

fof(f152,plain,
    ( ~ l1_struct_0(sK0)
    | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f151,f54])).

fof(f151,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) ),
    inference(resolution,[],[f150,f30])).

fof(f150,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,
    ( v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f148,f57])).

fof(f148,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f147,f30])).

fof(f147,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f145,f53])).

fof(f145,plain,
    ( v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f143,f49])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0))
      | v1_finset_1(sK2(sK0,sK3(sK0,X0)))
      | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f138,f30])).

fof(f138,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0))
      | v1_finset_1(sK2(sK0,sK3(sK0,X0)))
      | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f137,f53])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0))
      | v1_finset_1(sK2(sK0,sK3(sK0,X0)))
      | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f133,f50])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_setfam_1(X0,k2_struct_0(sK0))
      | v1_finset_1(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ) ),
    inference(resolution,[],[f131,f30])).

fof(f131,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_setfam_1(X3,k2_struct_0(sK0))
      | ~ v1_tops_2(X3,sK0)
      | v1_finset_1(sK2(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f130,f53])).

fof(f130,plain,(
    ! [X3] :
      ( ~ m1_setfam_1(X3,k2_struct_0(sK0))
      | ~ v1_tops_2(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_finset_1(sK2(sK0,X3))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f121,f53])).

fof(f121,plain,(
    ! [X3] :
      ( ~ v1_tops_2(X3,sK0)
      | ~ m1_setfam_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_finset_1(sK2(sK0,X3))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f116,f39])).

fof(f39,plain,(
    ! [X0,X3] :
      ( ~ v1_compts_1(X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_finset_1(sK2(X0,X3))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:02:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (30280)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.48  % (30280)Refutation not found, incomplete strategy% (30280)------------------------------
% 0.22/0.48  % (30280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30280)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (30280)Memory used [KB]: 6140
% 0.22/0.48  % (30280)Time elapsed: 0.007 s
% 0.22/0.48  % (30280)------------------------------
% 0.22/0.48  % (30280)------------------------------
% 0.22/0.50  % (30264)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (30263)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (30281)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (30265)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.22/0.51  % (30279)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.22/0.51  % (30261)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.22/0.52  % (30274)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.22/0.52  % (30260)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.22/0.52  % (30269)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.22/0.52  % (30278)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.22/0.52  % (30273)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.22/0.52  % (30283)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.22/0.52  % (30268)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.22/0.52  % (30271)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.22/0.52  % (30259)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.22/0.52  % (30269)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f194,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(resolution,[],[f193,f117])).
% 1.22/0.52  fof(f117,plain,(
% 1.22/0.52    ~v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(resolution,[],[f116,f32])).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ~v1_compts_1(sK0) | ~v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f19])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    (~v2_compts_1(k2_struct_0(sK0),sK0) | ~v1_compts_1(sK0)) & (v2_compts_1(k2_struct_0(sK0),sK0) | v1_compts_1(sK0)) & l1_pre_topc(sK0)),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    ? [X0] : ((~v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0)) & (v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0)) & l1_pre_topc(X0)) => ((~v2_compts_1(k2_struct_0(sK0),sK0) | ~v1_compts_1(sK0)) & (v2_compts_1(k2_struct_0(sK0),sK0) | v1_compts_1(sK0)) & l1_pre_topc(sK0))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f17,plain,(
% 1.22/0.52    ? [X0] : ((~v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0)) & (v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0)) & l1_pre_topc(X0))),
% 1.22/0.52    inference(flattening,[],[f16])).
% 1.22/0.52  fof(f16,plain,(
% 1.22/0.52    ? [X0] : (((~v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0)) & (v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0))) & l1_pre_topc(X0))),
% 1.22/0.52    inference(nnf_transformation,[],[f8])).
% 1.22/0.52  fof(f8,plain,(
% 1.22/0.52    ? [X0] : ((v1_compts_1(X0) <~> v2_compts_1(k2_struct_0(X0),X0)) & l1_pre_topc(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f7])).
% 1.22/0.52  fof(f7,negated_conjecture,(
% 1.22/0.52    ~! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 1.22/0.52    inference(negated_conjecture,[],[f6])).
% 1.22/0.52  fof(f6,conjecture,(
% 1.22/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).
% 1.22/0.52  fof(f116,plain,(
% 1.22/0.52    v1_compts_1(sK0)),
% 1.22/0.52    inference(resolution,[],[f115,f52])).
% 1.22/0.52  fof(f52,plain,(
% 1.22/0.52    l1_struct_0(sK0)),
% 1.22/0.52    inference(resolution,[],[f35,f30])).
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    l1_pre_topc(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f19])).
% 1.22/0.52  fof(f35,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.22/0.52  fof(f115,plain,(
% 1.22/0.52    ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.22/0.52    inference(resolution,[],[f113,f54])).
% 1.22/0.52  fof(f54,plain,(
% 1.22/0.52    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 1.22/0.52    inference(superposition,[],[f34,f53])).
% 1.22/0.52  fof(f53,plain,(
% 1.22/0.52    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.22/0.52    inference(resolution,[],[f33,f52])).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f9])).
% 1.22/0.52  fof(f9,plain,(
% 1.22/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.22/0.52  fof(f34,plain,(
% 1.22/0.52    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f10])).
% 1.22/0.52  fof(f10,plain,(
% 1.22/0.52    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 1.22/0.52  fof(f113,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0)),
% 1.22/0.52    inference(resolution,[],[f112,f30])).
% 1.22/0.52  fof(f112,plain,(
% 1.22/0.52    ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f111])).
% 1.22/0.52  fof(f111,plain,(
% 1.22/0.52    v1_compts_1(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f110,f56])).
% 1.22/0.52  fof(f56,plain,(
% 1.22/0.52    m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(superposition,[],[f40,f53])).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,sK1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(sK1(X0),X0) & m1_setfam_1(sK1(X0),u1_struct_0(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X3] : ((v1_finset_1(sK2(X0,X3)) & m1_setfam_1(sK2(X0,X3),u1_struct_0(X0)) & r1_tarski(sK2(X0,X3),X3) & m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f23,f22])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ! [X0] : (? [X1] : (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X1,X0) & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,sK1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(sK1(X0),X0) & m1_setfam_1(sK1(X0),u1_struct_0(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ! [X3,X0] : (? [X4] : (v1_finset_1(X4) & m1_setfam_1(X4,u1_struct_0(X0)) & r1_tarski(X4,X3) & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (v1_finset_1(sK2(X0,X3)) & m1_setfam_1(sK2(X0,X3),u1_struct_0(X0)) & r1_tarski(sK2(X0,X3),X3) & m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X1,X0) & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X3] : (? [X4] : (v1_finset_1(X4) & m1_setfam_1(X4,u1_struct_0(X0)) & r1_tarski(X4,X3) & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(rectify,[],[f20])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X1,X0) & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X1] : (? [X2] : (v1_finset_1(X2) & m1_setfam_1(X2,u1_struct_0(X0)) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X1,X0) | ~m1_setfam_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(nnf_transformation,[],[f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (v1_finset_1(X2) & m1_setfam_1(X2,u1_struct_0(X0)) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X1,X0) | ~m1_setfam_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(flattening,[],[f12])).
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : ((v1_finset_1(X2) & m1_setfam_1(X2,u1_struct_0(X0)) & r1_tarski(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X1,X0) | ~m1_setfam_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,axiom,(
% 1.22/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(v1_finset_1(X2) & m1_setfam_1(X2,u1_struct_0(X0)) & r1_tarski(X2,X1))) & v1_tops_2(X1,X0) & m1_setfam_1(X1,u1_struct_0(X0))))))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_compts_1)).
% 1.22/0.52  fof(f110,plain,(
% 1.22/0.52    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(resolution,[],[f109,f30])).
% 1.22/0.52  fof(f109,plain,(
% 1.22/0.52    ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f108])).
% 1.22/0.52  fof(f108,plain,(
% 1.22/0.52    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f107,f55])).
% 1.22/0.52  fof(f55,plain,(
% 1.22/0.52    m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(superposition,[],[f41,f53])).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    ( ! [X0] : (m1_setfam_1(sK1(X0),u1_struct_0(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f107,plain,(
% 1.22/0.52    ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f106])).
% 1.22/0.52  fof(f106,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f104,f42])).
% 1.22/0.52  fof(f42,plain,(
% 1.22/0.52    ( ! [X0] : (v1_tops_2(sK1(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f104,plain,(
% 1.22/0.52    ~v1_tops_2(sK1(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f103])).
% 1.22/0.52  fof(f103,plain,(
% 1.22/0.52    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_2(sK1(sK0),sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | v1_compts_1(sK0)),
% 1.22/0.52    inference(resolution,[],[f102,f31])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    v2_compts_1(k2_struct_0(sK0),sK0) | v1_compts_1(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f19])).
% 1.22/0.52  fof(f102,plain,(
% 1.22/0.52    ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_2(sK1(sK0),sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f101])).
% 1.22/0.52  fof(f101,plain,(
% 1.22/0.52    v1_compts_1(sK0) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_2(sK1(sK0),sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f100,f66])).
% 1.22/0.52  fof(f66,plain,(
% 1.22/0.52    ( ! [X0,X1] : (m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~m1_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(superposition,[],[f44,f53])).
% 1.22/0.52  fof(f44,plain,(
% 1.22/0.52    ( ! [X4,X0,X1] : (m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f29,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : (((v2_compts_1(X1,X0) | (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,sK3(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(sK3(X0,X1),X0) & m1_setfam_1(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X4] : ((v1_finset_1(sK4(X0,X1,X4)) & m1_setfam_1(sK4(X0,X1,X4),X1) & r1_tarski(sK4(X0,X1,X4),X4) & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f28,f27])).
% 1.22/0.52  fof(f27,plain,(
% 1.22/0.52    ! [X1,X0] : (? [X2] : (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X2,X0) & m1_setfam_1(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,sK3(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(sK3(X0,X1),X0) & m1_setfam_1(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f28,plain,(
% 1.22/0.52    ! [X4,X1,X0] : (? [X5] : (v1_finset_1(X5) & m1_setfam_1(X5,X1) & r1_tarski(X5,X4) & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (v1_finset_1(sK4(X0,X1,X4)) & m1_setfam_1(sK4(X0,X1,X4),X1) & r1_tarski(sK4(X0,X1,X4),X4) & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : (((v2_compts_1(X1,X0) | ? [X2] : (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X2,X0) & m1_setfam_1(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X4] : (? [X5] : (v1_finset_1(X5) & m1_setfam_1(X5,X1) & r1_tarski(X5,X4) & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(rectify,[],[f25])).
% 1.22/0.52  fof(f25,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : (((v2_compts_1(X1,X0) | ? [X2] : (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X2,X0) & m1_setfam_1(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X2] : (? [X3] : (v1_finset_1(X3) & m1_setfam_1(X3,X1) & r1_tarski(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X2,X0) | ~m1_setfam_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(nnf_transformation,[],[f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) <=> ! [X2] : (? [X3] : (v1_finset_1(X3) & m1_setfam_1(X3,X1) & r1_tarski(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X2,X0) | ~m1_setfam_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(flattening,[],[f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) <=> ! [X2] : ((? [X3] : ((v1_finset_1(X3) & m1_setfam_1(X3,X1) & r1_tarski(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X2,X0) | ~m1_setfam_1(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_compts_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(v1_finset_1(X3) & m1_setfam_1(X3,X1) & r1_tarski(X3,X2))) & v1_tops_2(X2,X0) & m1_setfam_1(X2,X1))))))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_compts_1)).
% 1.22/0.52  fof(f100,plain,(
% 1.22/0.52    ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(resolution,[],[f99,f30])).
% 1.22/0.52  fof(f99,plain,(
% 1.22/0.52    ~l1_pre_topc(sK0) | v1_compts_1(sK0) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f98])).
% 1.22/0.52  fof(f98,plain,(
% 1.22/0.52    v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f97,f55])).
% 1.22/0.52  fof(f97,plain,(
% 1.22/0.52    ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f96])).
% 1.22/0.52  fof(f96,plain,(
% 1.22/0.52    ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f94,f42])).
% 1.22/0.52  fof(f94,plain,(
% 1.22/0.52    ~v1_tops_2(sK1(sK0),sK0) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f93])).
% 1.22/0.52  fof(f93,plain,(
% 1.22/0.52    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~v1_tops_2(sK1(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0)),
% 1.22/0.52    inference(resolution,[],[f92,f31])).
% 1.22/0.52  fof(f92,plain,(
% 1.22/0.52    ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~v1_tops_2(sK1(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(forward_demodulation,[],[f91,f53])).
% 1.22/0.52  fof(f91,plain,(
% 1.22/0.52    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~v1_tops_2(sK1(sK0),sK0) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f90])).
% 1.22/0.52  fof(f90,plain,(
% 1.22/0.52    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v1_tops_2(sK1(sK0),sK0) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    inference(forward_demodulation,[],[f89,f53])).
% 1.22/0.52  fof(f89,plain,(
% 1.22/0.52    ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v1_tops_2(sK1(sK0),sK0) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f88])).
% 1.22/0.52  fof(f88,plain,(
% 1.22/0.52    ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v1_tops_2(sK1(sK0),sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f87,f46])).
% 1.22/0.52  fof(f46,plain,(
% 1.22/0.52    ( ! [X4,X0,X1] : (m1_setfam_1(sK4(X0,X1,X4),X1) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f87,plain,(
% 1.22/0.52    ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k2_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.22/0.52    inference(forward_demodulation,[],[f86,f53])).
% 1.22/0.52  fof(f86,plain,(
% 1.22/0.52    ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.22/0.52    inference(forward_demodulation,[],[f85,f53])).
% 1.22/0.52  fof(f85,plain,(
% 1.22/0.52    v1_compts_1(sK0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f84])).
% 1.22/0.52  fof(f84,plain,(
% 1.22/0.52    v1_compts_1(sK0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f83,f42])).
% 1.22/0.52  fof(f83,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f82,f52])).
% 1.22/0.52  fof(f82,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_struct_0(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_compts_1(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f79,f54])).
% 1.22/0.52  fof(f79,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))) )),
% 1.22/0.52    inference(resolution,[],[f78,f30])).
% 1.22/0.52  fof(f78,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f77])).
% 1.22/0.52  fof(f77,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_compts_1(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f71,f31])).
% 1.22/0.52  fof(f71,plain,(
% 1.22/0.52    ( ! [X0] : (~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f70,f53])).
% 1.22/0.52  fof(f70,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f69])).
% 1.22/0.52  fof(f69,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f68,f53])).
% 1.22/0.52  fof(f68,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f67])).
% 1.22/0.52  fof(f67,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(sK1(X0),sK0) | v1_compts_1(X0) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),u1_struct_0(X0)) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),sK1(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tops_2(sK1(X0),sK0) | ~m1_setfam_1(sK1(X0),k2_struct_0(sK0)) | ~m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f65,f45])).
% 1.22/0.52  fof(f45,plain,(
% 1.22/0.52    ( ! [X4,X0,X1] : (r1_tarski(sK4(X0,X1,X4),X4) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f65,plain,(
% 1.22/0.52    ( ! [X4,X3] : (~r1_tarski(sK4(sK0,k2_struct_0(sK0),X3),sK1(X4)) | ~m1_setfam_1(X3,k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(X3,sK0) | v1_compts_1(X4) | ~m1_setfam_1(sK4(sK0,k2_struct_0(sK0),X3),u1_struct_0(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,k2_struct_0(sK0),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4)))) | ~l1_pre_topc(X4)) )),
% 1.22/0.52    inference(resolution,[],[f63,f43])).
% 1.22/0.52  fof(f43,plain,(
% 1.22/0.52    ( ! [X2,X0] : (~v1_finset_1(X2) | v1_compts_1(X0) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,sK1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f63,plain,(
% 1.22/0.52    ( ! [X0] : (v1_finset_1(sK4(sK0,k2_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(X0,k2_struct_0(sK0)) | v1_compts_1(sK0) | ~v1_tops_2(X0,sK0)) )),
% 1.22/0.52    inference(resolution,[],[f62,f52])).
% 1.22/0.52  fof(f62,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_struct_0(sK0) | ~m1_setfam_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_finset_1(sK4(sK0,k2_struct_0(sK0),X0)) | v1_compts_1(sK0) | ~v1_tops_2(X0,sK0)) )),
% 1.22/0.52    inference(resolution,[],[f61,f54])).
% 1.22/0.52  fof(f61,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_2(X0,sK0) | ~m1_setfam_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_finset_1(sK4(sK0,k2_struct_0(sK0),X0)) | v1_compts_1(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f60,f31])).
% 1.22/0.52  fof(f60,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~v2_compts_1(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v1_tops_2(X0,sK0) | ~m1_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_finset_1(sK4(sK0,X1,X0))) )),
% 1.22/0.52    inference(forward_demodulation,[],[f59,f53])).
% 1.22/0.52  fof(f59,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v1_tops_2(X0,sK0) | ~m1_setfam_1(X0,X1) | ~v2_compts_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_finset_1(sK4(sK0,X1,X0))) )),
% 1.22/0.52    inference(forward_demodulation,[],[f58,f53])).
% 1.22/0.52  fof(f58,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~v1_tops_2(X0,sK0) | ~m1_setfam_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_compts_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_finset_1(sK4(sK0,X1,X0))) )),
% 1.22/0.52    inference(resolution,[],[f47,f30])).
% 1.22/0.52  fof(f47,plain,(
% 1.22/0.52    ( ! [X4,X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_finset_1(sK4(X0,X1,X4))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f193,plain,(
% 1.22/0.52    v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(resolution,[],[f192,f52])).
% 1.22/0.52  fof(f192,plain,(
% 1.22/0.52    ~l1_struct_0(sK0) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(resolution,[],[f191,f54])).
% 1.22/0.52  fof(f191,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(resolution,[],[f190,f30])).
% 1.22/0.52  fof(f190,plain,(
% 1.22/0.52    ~l1_pre_topc(sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f189])).
% 1.22/0.52  fof(f189,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f188,f57])).
% 1.22/0.52  fof(f57,plain,(
% 1.22/0.52    ( ! [X0] : (m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(superposition,[],[f48,f53])).
% 1.22/0.52  fof(f48,plain,(
% 1.22/0.52    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f188,plain,(
% 1.22/0.52    ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(resolution,[],[f187,f30])).
% 1.22/0.52  fof(f187,plain,(
% 1.22/0.52    ~l1_pre_topc(sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f186])).
% 1.22/0.52  fof(f186,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(forward_demodulation,[],[f185,f53])).
% 1.22/0.52  fof(f185,plain,(
% 1.22/0.52    ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f184])).
% 1.22/0.52  fof(f184,plain,(
% 1.22/0.52    ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f183,f49])).
% 1.22/0.52  fof(f49,plain,(
% 1.22/0.52    ( ! [X0,X1] : (m1_setfam_1(sK3(X0,X1),X1) | v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f183,plain,(
% 1.22/0.52    ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f182])).
% 1.22/0.52  fof(f182,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(forward_demodulation,[],[f181,f53])).
% 1.22/0.52  fof(f181,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f180])).
% 1.22/0.52  fof(f180,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | v2_compts_1(k2_struct_0(sK0),sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f179,f50])).
% 1.22/0.52  fof(f50,plain,(
% 1.22/0.52    ( ! [X0,X1] : (v1_tops_2(sK3(X0,X1),X0) | v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f179,plain,(
% 1.22/0.52    ~v1_tops_2(sK3(sK0,k2_struct_0(sK0)),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f178])).
% 1.22/0.52  fof(f178,plain,(
% 1.22/0.52    v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~v1_tops_2(sK3(sK0,k2_struct_0(sK0)),sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f177,f127])).
% 1.22/0.52  fof(f127,plain,(
% 1.22/0.52    ( ! [X1] : (m1_setfam_1(sK2(sK0,X1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(X1,k2_struct_0(sK0)) | ~v1_tops_2(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f126,f53])).
% 1.22/0.52  fof(f126,plain,(
% 1.22/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(X1,k2_struct_0(sK0)) | ~v1_tops_2(X1,sK0) | m1_setfam_1(sK2(sK0,X1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f125,f53])).
% 1.22/0.52  fof(f125,plain,(
% 1.22/0.52    ( ! [X1] : (~m1_setfam_1(X1,k2_struct_0(sK0)) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_setfam_1(sK2(sK0,X1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f119,f53])).
% 1.22/0.52  fof(f119,plain,(
% 1.22/0.52    ( ! [X1] : (~v1_tops_2(X1,sK0) | ~m1_setfam_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_setfam_1(sK2(sK0,X1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f116,f38])).
% 1.22/0.52  fof(f38,plain,(
% 1.22/0.52    ( ! [X0,X3] : (~v1_compts_1(X0) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_setfam_1(sK2(X0,X3),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f177,plain,(
% 1.22/0.52    ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f176])).
% 1.22/0.52  fof(f176,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(forward_demodulation,[],[f175,f53])).
% 1.22/0.52  fof(f175,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f174])).
% 1.22/0.52  fof(f174,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f173,f49])).
% 1.22/0.52  fof(f173,plain,(
% 1.22/0.52    ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f172])).
% 1.22/0.52  fof(f172,plain,(
% 1.22/0.52    ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f171,f142])).
% 1.22/0.52  fof(f142,plain,(
% 1.22/0.52    ( ! [X0] : (r1_tarski(sK2(sK0,sK3(sK0,X0)),sK3(sK0,X0)) | ~m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f141,f53])).
% 1.22/0.52  fof(f141,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0)) | r1_tarski(sK2(sK0,sK3(sK0,X0)),sK3(sK0,X0)) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f139,f50])).
% 1.22/0.52  fof(f139,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_tops_2(X0,sK0) | ~m1_setfam_1(X0,k2_struct_0(sK0)) | r1_tarski(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))) )),
% 1.22/0.52    inference(resolution,[],[f129,f30])).
% 1.22/0.52  fof(f129,plain,(
% 1.22/0.52    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_setfam_1(X2,k2_struct_0(sK0)) | ~v1_tops_2(X2,sK0) | r1_tarski(sK2(sK0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))) )),
% 1.22/0.52    inference(forward_demodulation,[],[f128,f53])).
% 1.22/0.52  fof(f128,plain,(
% 1.22/0.52    ( ! [X2] : (~m1_setfam_1(X2,k2_struct_0(sK0)) | ~v1_tops_2(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(sK2(sK0,X2),X2) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f120,f53])).
% 1.22/0.52  fof(f120,plain,(
% 1.22/0.52    ( ! [X2] : (~v1_tops_2(X2,sK0) | ~m1_setfam_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(sK2(sK0,X2),X2) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f116,f37])).
% 1.22/0.52  fof(f37,plain,(
% 1.22/0.52    ( ! [X0,X3] : (~v1_compts_1(X0) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r1_tarski(sK2(X0,X3),X3) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f171,plain,(
% 1.22/0.52    ( ! [X0] : (~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | v2_compts_1(X0,sK0)) )),
% 1.22/0.52    inference(resolution,[],[f170,f52])).
% 1.22/0.52  fof(f170,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_struct_0(sK0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | v2_compts_1(X0,sK0)) )),
% 1.22/0.52    inference(resolution,[],[f169,f54])).
% 1.22/0.52  fof(f169,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0)) )),
% 1.22/0.52    inference(resolution,[],[f168,f30])).
% 1.22/0.52  fof(f168,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0)) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f167])).
% 1.22/0.52  fof(f167,plain,(
% 1.22/0.52    ( ! [X0] : (v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f166,f57])).
% 1.22/0.52  fof(f166,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.22/0.52    inference(resolution,[],[f165,f30])).
% 1.22/0.52  fof(f165,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f164])).
% 1.22/0.52  fof(f164,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f163,f53])).
% 1.22/0.52  fof(f163,plain,(
% 1.22/0.52    ( ! [X0] : (~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f162])).
% 1.22/0.52  fof(f162,plain,(
% 1.22/0.52    ( ! [X0] : (~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~l1_pre_topc(sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f161,f49])).
% 1.22/0.52  fof(f161,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f160,f53])).
% 1.22/0.52  fof(f160,plain,(
% 1.22/0.52    ( ! [X0] : (~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f159])).
% 1.22/0.52  fof(f159,plain,(
% 1.22/0.52    ( ! [X0] : (~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~l1_pre_topc(sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f158,f50])).
% 1.22/0.52  fof(f158,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_tops_2(sK3(sK0,k2_struct_0(sK0)),sK0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK3(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f157,f124])).
% 1.22/0.52  fof(f124,plain,(
% 1.22/0.52    ( ! [X0] : (m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(X0,k2_struct_0(sK0)) | ~v1_tops_2(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f123,f53])).
% 1.22/0.52  fof(f123,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(X0,k2_struct_0(sK0)) | ~v1_tops_2(X0,sK0) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f122,f53])).
% 1.22/0.52  fof(f122,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_setfam_1(X0,k2_struct_0(sK0)) | ~v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f118,f53])).
% 1.22/0.52  fof(f118,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_tops_2(X0,sK0) | ~m1_setfam_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f116,f36])).
% 1.22/0.52  fof(f36,plain,(
% 1.22/0.52    ( ! [X0,X3] : (~v1_compts_1(X0) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f157,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK0)) )),
% 1.22/0.52    inference(resolution,[],[f156,f30])).
% 1.22/0.52  fof(f156,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | v2_compts_1(X0,sK0) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(sK0,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))) )),
% 1.22/0.52    inference(superposition,[],[f154,f53])).
% 1.22/0.52  fof(f154,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | v2_compts_1(X0,X1) | ~m1_setfam_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),X0) | ~r1_tarski(sK2(sK0,sK3(sK0,k2_struct_0(sK0))),sK3(X1,X0)) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 1.22/0.52    inference(resolution,[],[f153,f51])).
% 1.22/0.52  fof(f51,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (~v1_finset_1(X3) | v2_compts_1(X1,X0) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,sK3(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f153,plain,(
% 1.22/0.52    v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(resolution,[],[f152,f52])).
% 1.22/0.52  fof(f152,plain,(
% 1.22/0.52    ~l1_struct_0(sK0) | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0)),
% 1.22/0.52    inference(resolution,[],[f151,f54])).
% 1.22/0.52  fof(f151,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))),
% 1.22/0.52    inference(resolution,[],[f150,f30])).
% 1.22/0.52  fof(f150,plain,(
% 1.22/0.52    ~l1_pre_topc(sK0) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0))))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f149])).
% 1.22/0.52  fof(f149,plain,(
% 1.22/0.52    v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f148,f57])).
% 1.22/0.52  fof(f148,plain,(
% 1.22/0.52    ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(resolution,[],[f147,f30])).
% 1.22/0.52  fof(f147,plain,(
% 1.22/0.52    ~l1_pre_topc(sK0) | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f146])).
% 1.22/0.52  fof(f146,plain,(
% 1.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(forward_demodulation,[],[f145,f53])).
% 1.22/0.52  fof(f145,plain,(
% 1.22/0.52    v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f144])).
% 1.22/0.52  fof(f144,plain,(
% 1.22/0.52    v1_finset_1(sK2(sK0,sK3(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK3(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.22/0.52    inference(resolution,[],[f143,f49])).
% 1.22/0.52  fof(f143,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0)) | v1_finset_1(sK2(sK0,sK3(sK0,X0))) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.22/0.52    inference(resolution,[],[f138,f30])).
% 1.22/0.52  fof(f138,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0)) | v1_finset_1(sK2(sK0,sK3(sK0,X0))) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.22/0.52    inference(forward_demodulation,[],[f137,f53])).
% 1.22/0.52  fof(f137,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_setfam_1(sK3(sK0,X0),k2_struct_0(sK0)) | v1_finset_1(sK2(sK0,sK3(sK0,X0))) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f133,f50])).
% 1.22/0.52  fof(f133,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_tops_2(X0,sK0) | ~m1_setfam_1(X0,k2_struct_0(sK0)) | v1_finset_1(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))) )),
% 1.22/0.52    inference(resolution,[],[f131,f30])).
% 1.22/0.52  fof(f131,plain,(
% 1.22/0.52    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_setfam_1(X3,k2_struct_0(sK0)) | ~v1_tops_2(X3,sK0) | v1_finset_1(sK2(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))) )),
% 1.22/0.52    inference(forward_demodulation,[],[f130,f53])).
% 1.22/0.52  fof(f130,plain,(
% 1.22/0.52    ( ! [X3] : (~m1_setfam_1(X3,k2_struct_0(sK0)) | ~v1_tops_2(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_finset_1(sK2(sK0,X3)) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f121,f53])).
% 1.22/0.52  fof(f121,plain,(
% 1.22/0.52    ( ! [X3] : (~v1_tops_2(X3,sK0) | ~m1_setfam_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_finset_1(sK2(sK0,X3)) | ~l1_pre_topc(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f116,f39])).
% 1.22/0.52  fof(f39,plain,(
% 1.22/0.52    ( ! [X0,X3] : (~v1_compts_1(X0) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_finset_1(sK2(X0,X3)) | ~l1_pre_topc(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (30269)------------------------------
% 1.22/0.52  % (30269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (30269)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (30269)Memory used [KB]: 1791
% 1.22/0.52  % (30269)Time elapsed: 0.096 s
% 1.22/0.52  % (30269)------------------------------
% 1.22/0.52  % (30269)------------------------------
% 1.22/0.53  % (30258)Success in time 0.16 s
%------------------------------------------------------------------------------
