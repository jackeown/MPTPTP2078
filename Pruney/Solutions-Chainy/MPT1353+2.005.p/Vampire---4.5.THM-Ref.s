%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 (1167 expanded)
%              Number of leaves         :   10 ( 325 expanded)
%              Depth                    :   27
%              Number of atoms          :  326 (6203 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(subsumption_resolution,[],[f265,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
      | ~ v1_tops_2(sK1,sK0) )
    & ( r1_tarski(sK1,u1_pre_topc(sK0))
      | v1_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(sK0))
            | ~ v1_tops_2(X1,sK0) )
          & ( r1_tarski(X1,u1_pre_topc(sK0))
            | v1_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,u1_pre_topc(sK0))
          | ~ v1_tops_2(X1,sK0) )
        & ( r1_tarski(X1,u1_pre_topc(sK0))
          | v1_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
        | ~ v1_tops_2(sK1,sK0) )
      & ( r1_tarski(sK1,u1_pre_topc(sK0))
        | v1_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> r1_tarski(X1,u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f265,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f260,f44])).

fof(f44,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f260,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f257,f173])).

fof(f173,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3(X2,sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f163,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK3(X0,X1,X2),X2)
            & r2_hidden(sK3(X0,X1,X2),X1)
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f163,plain,(
    ~ r1_tarski(sK1,u1_pre_topc(sK0)) ),
    inference(resolution,[],[f158,f32])).

fof(f32,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ r1_tarski(sK1,u1_pre_topc(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f158,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f157,f30])).

fof(f157,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(sK1,sK0) ),
    inference(resolution,[],[f145,f31])).

fof(f31,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_pre_topc(sK0))
      | v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(global_subsumption,[],[f96,f131,f144])).

fof(f144,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_2(X0,sK0)
      | ~ r1_tarski(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f143,f29])).

fof(f143,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_2(X0,sK0)
      | ~ r1_tarski(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f44])).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_2(X0,sK0)
      | ~ r1_tarski(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f97,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f97,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f86,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f131,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f130,f99])).

fof(f99,plain,
    ( ~ v3_pre_topc(sK2(sK0,u1_pre_topc(sK0)),sK0)
    | v1_tops_2(u1_pre_topc(sK0),sK0) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ v3_pre_topc(sK2(sK0,u1_pre_topc(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f130,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | v3_pre_topc(sK2(sK0,u1_pre_topc(sK0)),sK0)
    | ~ m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f128,f29])).

fof(f128,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | v3_pre_topc(sK2(sK0,u1_pre_topc(sK0)),sK0)
    | ~ m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f98,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f98,plain,
    ( r2_hidden(sK2(sK0,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | v1_tops_2(u1_pre_topc(sK0),sK0) ),
    inference(subsumption_resolution,[],[f87,f29])).

fof(f87,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | r2_hidden(sK2(sK0,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X1] :
      ( v1_tops_2(X1,sK0)
      | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
      | ~ r1_tarski(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f84,f29])).

fof(f84,plain,(
    ! [X1] :
      ( v1_tops_2(X1,sK0)
      | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
      | ~ r1_tarski(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f44,f40])).

fof(f257,plain,(
    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f255,f202])).

fof(f202,plain,(
    m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f201,f44])).

fof(f201,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f171,f30])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,sK1,u1_pre_topc(sK0)),X0) ) ),
    inference(resolution,[],[f163,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f255,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f254,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f254,plain,(
    v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f203,f222])).

fof(f222,plain,(
    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f221,f29])).

fof(f221,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f217,f163])).

fof(f217,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1)
    | r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f33])).

fof(f60,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X5),sK1)
      | r1_tarski(sK1,X5) ) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f203,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1)
    | v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0) ),
    inference(resolution,[],[f202,f169])).

fof(f169,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK1)
      | v3_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f168,f29])).

fof(f168,plain,(
    ! [X1] :
      ( v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f30])).

fof(f165,plain,(
    ! [X1] :
      ( v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f158,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (17315)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.48  % (17315)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f265,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ((~r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)) & (r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,u1_pre_topc(sK0)) | ~v1_tops_2(X1,sK0)) & (r1_tarski(X1,u1_pre_topc(sK0)) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X1] : ((~r1_tarski(X1,u1_pre_topc(sK0)) | ~v1_tops_2(X1,sK0)) & (r1_tarski(X1,u1_pre_topc(sK0)) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => ((~r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)) & (r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> r1_tarski(X1,u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    inference(subsumption_resolution,[],[f260,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    inference(resolution,[],[f29,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    inference(resolution,[],[f257,f173])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(sK3(X2,sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(X2))) )),
% 0.20/0.48    inference(resolution,[],[f163,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    ~r1_tarski(sK1,u1_pre_topc(sK0))),
% 0.20/0.48    inference(resolution,[],[f158,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ~v1_tops_2(sK1,sK0) | ~r1_tarski(sK1,u1_pre_topc(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f157,f30])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    v1_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f156])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    v1_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f145,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,u1_pre_topc(sK0)) | v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.20/0.48    inference(global_subsumption,[],[f96,f131,f144])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(X0,sK0) | ~r1_tarski(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f143,f29])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(X0,sK0) | ~r1_tarski(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f141,f44])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(X0,sK0) | ~r1_tarski(X0,u1_pre_topc(sK0)) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f97,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    v1_tops_2(u1_pre_topc(sK0),sK0) | m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f86,f29])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    v1_tops_2(u1_pre_topc(sK0),sK0) | m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.48    inference(resolution,[],[f44,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(rectify,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    v1_tops_2(u1_pre_topc(sK0),sK0) | ~m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f130,f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ~v3_pre_topc(sK2(sK0,u1_pre_topc(sK0)),sK0) | v1_tops_2(u1_pre_topc(sK0),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f88,f29])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    v1_tops_2(u1_pre_topc(sK0),sK0) | ~v3_pre_topc(sK2(sK0,u1_pre_topc(sK0)),sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.48    inference(resolution,[],[f44,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    v1_tops_2(u1_pre_topc(sK0),sK0) | v3_pre_topc(sK2(sK0,u1_pre_topc(sK0)),sK0) | ~m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f128,f29])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    v1_tops_2(u1_pre_topc(sK0),sK0) | v3_pre_topc(sK2(sK0,u1_pre_topc(sK0)),sK0) | ~m1_subset_1(sK2(sK0,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.48    inference(resolution,[],[f98,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | v1_tops_2(u1_pre_topc(sK0),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f87,f29])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    v1_tops_2(u1_pre_topc(sK0),sK0) | r2_hidden(sK2(sK0,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.20/0.48    inference(resolution,[],[f44,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X1] : (v1_tops_2(X1,sK0) | ~v1_tops_2(u1_pre_topc(sK0),sK0) | ~r1_tarski(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f29])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X1] : (v1_tops_2(X1,sK0) | ~v1_tops_2(u1_pre_topc(sK0),sK0) | ~r1_tarski(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f44,f40])).
% 0.20/0.48  fof(f257,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f255,f202])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f201,f44])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(resolution,[],[f171,f30])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,sK1,u1_pre_topc(sK0)),X0)) )),
% 0.20/0.48    inference(resolution,[],[f163,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK3(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f255,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | ~m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(resolution,[],[f254,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(X0,sK0) | r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.48    inference(resolution,[],[f29,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f203,f222])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f221,f29])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f217,f163])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1) | r1_tarski(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.20/0.48    inference(resolution,[],[f60,f33])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X5),sK1) | r1_tarski(sK1,X5)) )),
% 0.20/0.48    inference(resolution,[],[f30,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    ~r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1) | v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0)),
% 0.20/0.48    inference(resolution,[],[f202,f169])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK1) | v3_pre_topc(X1,sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f168,f29])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    ( ! [X1] : (v3_pre_topc(X1,sK0) | ~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f165,f30])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    ( ! [X1] : (v3_pre_topc(X1,sK0) | ~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f158,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17315)------------------------------
% 0.20/0.48  % (17315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17315)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17315)Memory used [KB]: 5500
% 0.20/0.48  % (17315)Time elapsed: 0.075 s
% 0.20/0.48  % (17315)------------------------------
% 0.20/0.48  % (17315)------------------------------
% 0.20/0.48  % (17323)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.49  % (17303)Success in time 0.128 s
%------------------------------------------------------------------------------
