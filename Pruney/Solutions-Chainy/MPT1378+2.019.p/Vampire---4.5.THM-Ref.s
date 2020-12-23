%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 531 expanded)
%              Number of leaves         :   12 ( 212 expanded)
%              Depth                    :   49
%              Number of atoms          :  585 (4571 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   14 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f118,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    & m1_connsp_2(sK3,sK0,sK1)
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    & m1_connsp_2(X3,X0,X1)
                    & m1_connsp_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  & m1_connsp_2(X3,sK0,X1)
                  & m1_connsp_2(X2,sK0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                & m1_connsp_2(X3,sK0,X1)
                & m1_connsp_2(X2,sK0,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              & m1_connsp_2(X3,sK0,sK1)
              & m1_connsp_2(X2,sK0,sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
            & m1_connsp_2(X3,sK0,sK1)
            & m1_connsp_2(X2,sK0,sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          & m1_connsp_2(X3,sK0,sK1)
          & m1_connsp_2(sK2,sK0,sK1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
        & m1_connsp_2(X3,sK0,sK1)
        & m1_connsp_2(sK2,sK0,sK1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      & m1_connsp_2(sK3,sK0,sK1)
      & m1_connsp_2(sK2,sK0,sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).

fof(f118,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f115,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f39])).

fof(f39,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f113,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f111,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f111,plain,(
    ~ r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f110,f33])).

fof(f110,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f109,f34])).

fof(f109,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f108,f37])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f107,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f104,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK4(X0,X1,X2))
                & r1_tarski(sK4(X0,X1,X2),X2)
                & v3_pre_topc(sK4(X0,X1,X2),X0)
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK4(X0,X1,X2))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f104,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(sK0,sK1,X0),sK3)
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f102,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(sK0,sK1,X0),k2_xboole_0(sK2,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f101,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X0),k2_xboole_0(sK2,sK3))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X0),k2_xboole_0(sK2,sK3))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f98,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f98,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X1),k2_xboole_0(sK2,sK3))
      | ~ m1_connsp_2(X1,sK0,sK1) ) ),
    inference(resolution,[],[f96,f57])).

fof(f57,plain,(
    ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(subsumption_resolution,[],[f56,f36])).

fof(f56,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f53,f37])).

fof(f53,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f40,f51])).

fof(f40,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X4,X5] :
      ( m1_connsp_2(X4,sK0,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_connsp_2(X5,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f95,f32])).

fof(f95,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_connsp_2(X5,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f33])).

fof(f94,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_connsp_2(X5,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f34])).

fof(f93,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_connsp_2(X5,sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f35])).

fof(f91,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_connsp_2(X5,sK0,sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f52])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1)
      | ~ r1_tarski(sK4(sK0,sK1,X0),X1) ) ),
    inference(subsumption_resolution,[],[f85,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f60,f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f58,f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(sK0,sK1,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1)
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f84,f33])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(sK0,sK1,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1)
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f83,f34])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(sK0,sK1,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1)
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(sK0,sK1,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1)
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ m1_connsp_2(X5,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f79,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ m1_connsp_2(X5,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ m1_connsp_2(X5,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f34])).

fof(f77,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ m1_connsp_2(X5,sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f75,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X5),X4)
      | ~ m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X4,sK0,sK1)
      | ~ m1_connsp_2(X5,sK0,sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f52])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X0),X1)
      | ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X0),X1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f71,f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X0),X1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,sK1,X0),X1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK4(X0,X1,X2))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1,sK4(sK0,X0,X1))
      | ~ m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,X0,X1),X2)
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X2,sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1,sK4(sK0,X0,X1))
      | ~ m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,X0,X1),X2)
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X2,sK0,sK1) ) ),
    inference(resolution,[],[f67,f61])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k1_tops_1(sK0,X2))
      | ~ r2_hidden(X3,sK4(sK0,X0,X1))
      | ~ m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(sK0,X0,X1),X2)
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f66,f33])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK4(sK0,X0,X1),X2)
      | ~ r2_hidden(X3,sK4(sK0,X0,X1))
      | ~ m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,k1_tops_1(sK0,X2))
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f65,f34])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK4(sK0,X0,X1),X2)
      | ~ r2_hidden(X3,sK4(sK0,X0,X1))
      | ~ m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,k1_tops_1(sK0,X2))
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_tops_1(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f63,f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_tops_1(sK0,X2))
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f47,f34])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (771)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.46  % (760)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.46  % (760)Refutation not found, incomplete strategy% (760)------------------------------
% 0.21/0.46  % (760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (760)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (760)Memory used [KB]: 10490
% 0.21/0.46  % (760)Time elapsed: 0.055 s
% 0.21/0.46  % (760)------------------------------
% 0.21/0.46  % (760)------------------------------
% 0.21/0.48  % (754)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.48  % (750)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (749)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (764)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (773)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (758)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (766)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (776)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (759)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (769)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (767)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (776)Refutation not found, incomplete strategy% (776)------------------------------
% 0.21/0.51  % (776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (776)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (776)Memory used [KB]: 10618
% 0.21/0.51  % (776)Time elapsed: 0.108 s
% 0.21/0.51  % (776)------------------------------
% 0.21/0.51  % (776)------------------------------
% 0.21/0.51  % (772)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (772)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f116,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f115,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    m1_connsp_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f111,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f41,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f110,f33])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f109,f34])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f107,f39])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f104,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(sK4(X0,X1,X2),X2) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK4(X0,X1,X2)) & r1_tarski(sK4(X0,X1,X2),X2) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4(X0,X1,X2)) & r1_tarski(sK4(X0,X1,X2),X2) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(rectify,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK4(sK0,sK1,X0),sK3) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(resolution,[],[f102,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK4(sK0,sK1,X0),k2_xboole_0(sK2,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X0),k2_xboole_0(sK2,sK3)) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f99,f37])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X0),k2_xboole_0(sK2,sK3)) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(resolution,[],[f98,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(superposition,[],[f50,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X1),k2_xboole_0(sK2,sK3)) | ~m1_connsp_2(X1,sK0,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f96,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f56,f36])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f53,f37])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(superposition,[],[f40,f51])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X4,X5] : (m1_connsp_2(X4,sK0,sK1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_connsp_2(X5,sK0,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f32])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_connsp_2(X5,sK0,sK1) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f94,f33])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_connsp_2(X5,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f34])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_connsp_2(X5,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f91,f35])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_connsp_2(X5,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f86,f52])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1) | ~r1_tarski(sK4(sK0,sK1,X0),X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f60,f35])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f59,f33])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f58,f34])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0)) )),
% 0.21/0.51    inference(resolution,[],[f42,f32])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(sK4(sK0,sK1,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1) | ~m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f84,f33])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(sK4(sK0,sK1,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1) | ~m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f34])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(sK4(sK0,sK1,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1) | ~m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(sK4(sK0,sK1,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1) | ~m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f80,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~m1_connsp_2(X5,sK0,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f79,f32])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~m1_connsp_2(X5,sK0,sK1) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f33])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~m1_connsp_2(X5,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f77,f34])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~m1_connsp_2(X5,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f35])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X5),X4) | ~m1_subset_1(sK4(sK0,sK1,X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X4,sK0,sK1) | ~m1_connsp_2(X5,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f73,f52])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X0),X1) | ~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f33])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X0),X1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f34])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X0),X1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,sK1,X0),X1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f69,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,sK4(X0,X1,X2)) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK1,sK4(sK0,X0,X1)) | ~m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,X0,X1),X2) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X2,sK0,sK1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK1,sK4(sK0,X0,X1)) | ~m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,X0,X1),X2) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X2,sK0,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f67,f61])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k1_tops_1(sK0,X2)) | ~r2_hidden(X3,sK4(sK0,X0,X1)) | ~m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK0,X0,X1),X2) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f66,f33])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK4(sK0,X0,X1),X2) | ~r2_hidden(X3,sK4(sK0,X0,X1)) | ~m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,k1_tops_1(sK0,X2)) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f65,f34])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK4(sK0,X0,X1),X2) | ~r2_hidden(X3,sK4(sK0,X0,X1)) | ~m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,k1_tops_1(sK0,X2)) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f64,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,sK0) | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k1_tops_1(sK0,X2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f63,f33])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k1_tops_1(sK0,X2)) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f47,f34])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (772)------------------------------
% 0.21/0.51  % (772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (772)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (772)Memory used [KB]: 6268
% 0.21/0.51  % (772)Time elapsed: 0.111 s
% 0.21/0.51  % (772)------------------------------
% 0.21/0.51  % (772)------------------------------
% 0.21/0.51  % (768)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (752)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (748)Success in time 0.157 s
%------------------------------------------------------------------------------
