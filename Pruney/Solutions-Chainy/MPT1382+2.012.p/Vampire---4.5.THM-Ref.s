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
% DateTime   : Thu Dec  3 13:15:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 370 expanded)
%              Number of leaves         :   13 ( 137 expanded)
%              Depth                    :   24
%              Number of atoms          :  350 (3690 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(subsumption_resolution,[],[f197,f105])).

fof(f105,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f97,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_connsp_2(X3,sK0,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | v1_xboole_0(X3) )
                & m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_connsp_2(X3,sK0,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_connsp_2(X3,sK0,sK1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_connsp_2(X3,sK0,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ! [X3] :
          ( ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_connsp_2(X3,sK0,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
          | v1_xboole_0(X3) )
      & m1_connsp_2(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f97,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f197,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f182,f111])).

fof(f111,plain,(
    ! [X1] :
      ( r1_tarski(X1,u1_struct_0(sK0))
      | ~ r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f98,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f98,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f182,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f131,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f130,f92])).

fof(f92,plain,(
    r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f91,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f89,f36])).

fof(f89,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f87,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f39,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f39,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f130,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f129,f99])).

fof(f99,plain,(
    k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f93,f36])).

fof(f93,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f129,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f128,f34])).

fof(f128,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f127,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f36])).

fof(f126,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f37])).

fof(f125,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f119,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,(
    ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f118,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f77,f34])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f73,f36])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f118,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f117,f114])).

fof(f114,plain,(
    ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f92,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f117,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f116,f105])).

fof(f116,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f101,f40])).

fof(f40,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f94,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f38,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (8520)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.48  % (8504)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (8509)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (8501)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (8512)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (8517)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (8499)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (8509)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (8502)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (8521)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % (8500)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (8513)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.51  % (8505)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (8507)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (8521)Refutation not found, incomplete strategy% (8521)------------------------------
% 0.20/0.51  % (8521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8521)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8521)Memory used [KB]: 10618
% 0.20/0.51  % (8521)Time elapsed: 0.054 s
% 0.20/0.51  % (8521)------------------------------
% 0.20/0.51  % (8521)------------------------------
% 0.20/0.51  % (8518)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (8515)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (8503)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.51  % (8510)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f197,f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f97,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f26,f25,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f38,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    ~r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.51    inference(resolution,[],[f182,f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(X1,sK2)) )),
% 0.20/0.51    inference(resolution,[],[f98,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f38,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f131,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f130,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f91,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f90,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f89,f36])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f88,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f87,f38])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f39,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(forward_demodulation,[],[f129,f99])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f93,f36])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f38,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f128,f34])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f127,f35])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f126,f36])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f125,f37])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f119,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f118,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f77,f34])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f76,f35])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f73,f36])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f37,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f117,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.20/0.51    inference(resolution,[],[f92,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(rectify,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f116,f105])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.20/0.51    inference(resolution,[],[f101,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f100,f35])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f94,f36])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f38,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (8509)------------------------------
% 0.20/0.51  % (8509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8509)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (8509)Memory used [KB]: 1663
% 0.20/0.51  % (8509)Time elapsed: 0.089 s
% 0.20/0.51  % (8509)------------------------------
% 0.20/0.51  % (8509)------------------------------
% 0.20/0.51  % (8505)Refutation not found, incomplete strategy% (8505)------------------------------
% 0.20/0.51  % (8505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8516)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (8497)Success in time 0.155 s
%------------------------------------------------------------------------------
