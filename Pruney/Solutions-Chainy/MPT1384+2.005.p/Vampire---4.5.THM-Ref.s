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
% DateTime   : Thu Dec  3 13:15:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 (2928 expanded)
%              Number of leaves         :   10 ( 560 expanded)
%              Depth                    :   20
%              Number of atoms          :  307 (19929 expanded)
%              Number of equality atoms :   20 ( 324 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f965,plain,(
    $false ),
    inference(global_subsumption,[],[f555,f963])).

fof(f963,plain,(
    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) ),
    inference(unit_resulting_resolution,[],[f40,f39,f38,f313,f339,f340,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f340,plain,(
    m1_connsp_2(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f293,f314,f313,f32])).

fof(f32,plain,(
    ! [X2] :
      ( m1_connsp_2(sK3(X2),sK0,X2)
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f314,plain,(
    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f37,f78,f310,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f310,plain,(
    ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f72,f295,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f295,plain,(
    sK1 != k1_tops_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f40,f39,f40,f78,f37,f293,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X0,X2) != X2
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f72,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f40,f37,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f78,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f37,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f293,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f36,f291])).

fof(f291,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f219,f267])).

fof(f267,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f40,f39,f262])).

fof(f262,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f259,f78])).

fof(f259,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | ~ v3_pre_topc(sK1,sK0)
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(global_subsumption,[],[f40,f255])).

fof(f255,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ v2_pre_topc(X6)
      | ~ v3_pre_topc(sK1,sK0)
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f219,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f35,f217])).

fof(f217,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f210,f87])).

% (5840)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f87,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f72,f85])).

fof(f85,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f78,f34])).

fof(f34,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f210,plain,(
    ! [X3] :
      ( m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,k1_tops_1(sK0,sK1)) ) ),
    inference(global_subsumption,[],[f40,f39,f38,f209])).

fof(f209,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_tops_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X3) ) ),
    inference(forward_demodulation,[],[f204,f93])).

fof(f93,plain,(
    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f37,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f204,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X3,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))
      | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X3) ) ),
    inference(resolution,[],[f43,f78])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f339,plain,(
    m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f293,f314,f313,f31])).

fof(f31,plain,(
    ! [X2] :
      ( m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f313,plain,(
    m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f78,f310,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f555,plain,(
    ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) ),
    inference(unit_resulting_resolution,[],[f315,f402,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f402,plain,(
    r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f37,f326,f339,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

% (5850)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f326,plain,(
    r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f293,f310,f37,f78,f314,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK3(sK4(u1_struct_0(sK0),X1,X0)),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X1,X0)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),X1,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f315,plain,(
    ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f78,f310,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:19:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (5847)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (5839)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (5825)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (5824)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (5831)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (5830)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (5829)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (5847)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (5823)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f965,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(global_subsumption,[],[f555,f963])).
% 0.20/0.53  fof(f963,plain,(
% 0.20/0.53    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f40,f39,f38,f313,f339,f340,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.53  fof(f340,plain,(
% 0.20/0.53    m1_connsp_2(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f293,f314,f313,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X2] : (m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f11])).
% 0.20/0.53  fof(f11,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f37,f78,f310,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.53  fof(f310,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f72,f295,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f295,plain,(
% 0.20/0.53    sK1 != k1_tops_1(sK0,sK1)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f40,f39,f40,f78,f37,f293,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k1_tops_1(X0,X2) != X2 | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X0) | v3_pre_topc(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f40,f37,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f40,f37,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f293,plain,(
% 0.20/0.53    ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(global_subsumption,[],[f36,f291])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f277])).
% 0.20/0.53  fof(f277,plain,(
% 0.20/0.53    ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(superposition,[],[f219,f267])).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(global_subsumption,[],[f40,f39,f262])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f259,f78])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | ~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1)) )),
% 0.20/0.53    inference(global_subsumption,[],[f40,f255])).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    ( ! [X6,X7] : (~l1_pre_topc(X6) | ~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~v2_pre_topc(X6) | ~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1)) )),
% 0.20/0.53    inference(resolution,[],[f47,f37])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    ~r2_hidden(sK2,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(global_subsumption,[],[f35,f217])).
% 0.20/0.53  fof(f217,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK2,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f210,f87])).
% 0.20/0.53  % (5840)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ~m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(global_subsumption,[],[f72,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ~m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f78,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    ( ! [X3] : (m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,k1_tops_1(sK0,sK1))) )),
% 0.20/0.53    inference(global_subsumption,[],[f40,f39,f38,f209])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    ( ! [X3] : (~r2_hidden(X3,k1_tops_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X3)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f204,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f40,f37,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X3,k1_tops_1(sK0,k1_tops_1(sK0,sK1))) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X3)) )),
% 0.20/0.53    inference(resolution,[],[f43,f78])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f293,f314,f313,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X2] : (m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f313,plain,(
% 0.20/0.53    m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f37,f78,f310,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f555,plain,(
% 0.20/0.54    ~r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f315,f402,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f402,plain,(
% 0.20/0.54    r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f40,f37,f326,f339,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.20/0.54  % (5850)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  fof(f326,plain,(
% 0.20/0.54    r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f293,f310,f37,f78,f314,f114])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(sK3(sK4(u1_struct_0(sK0),X1,X0)),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,X0) | ~r2_hidden(sK4(u1_struct_0(sK0),X1,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.54    inference(resolution,[],[f48,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | r1_tarski(sK3(X2),sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f315,plain,(
% 0.20/0.54    ~r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f37,f78,f310,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (5847)------------------------------
% 0.20/0.54  % (5847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5847)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (5847)Memory used [KB]: 7291
% 0.20/0.54  % (5847)Time elapsed: 0.117 s
% 0.20/0.54  % (5847)------------------------------
% 0.20/0.54  % (5847)------------------------------
% 0.20/0.54  % (5822)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (5818)Success in time 0.176 s
%------------------------------------------------------------------------------
