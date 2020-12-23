%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:07 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  147 (5174 expanded)
%              Number of leaves         :   11 ( 918 expanded)
%              Depth                    :   45
%              Number of atoms          :  608 (33123 expanded)
%              Number of equality atoms :    5 (  42 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2821,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2820,f2335])).

fof(f2335,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f91,f2329])).

fof(f2329,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f2313,f99])).

fof(f99,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f89,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f79,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f44,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f2313,plain,(
    r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2312,f44])).

fof(f2312,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2311,f92])).

fof(f92,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f81,f47])).

fof(f81,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f2311,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f2306])).

fof(f2306,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1880,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f1880,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1879])).

fof(f1879,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1174,f1185])).

fof(f1185,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1168,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1168,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1144,f298])).

fof(f298,plain,
    ( r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f297,f149])).

fof(f149,plain,
    ( v3_pre_topc(sK1,sK0)
    | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f144,f140])).

fof(f140,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f85,f92])).

fof(f85,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK4(u1_struct_0(sK0),sK1,X1),u1_struct_0(sK0))
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f44,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f144,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f114,f40])).

fof(f40,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f114,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f92,f86])).

fof(f86,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X2),sK1)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f297,plain,
    ( r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f296,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f296,plain,
    ( r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f293,f44])).

fof(f293,plain,
    ( r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f292,f41])).

fof(f41,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(X3,sK0,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f292,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f287,f164])).

fof(f164,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) ),
    inference(resolution,[],[f149,f42])).

fof(f42,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f287,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | m1_connsp_2(sK1,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | m1_connsp_2(sK1,sK0,sK2)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) ),
    inference(resolution,[],[f171,f165])).

fof(f165,plain,
    ( r2_hidden(sK2,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) ),
    inference(resolution,[],[f149,f43])).

fof(f43,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f170,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f170,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f169,f44])).

fof(f169,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f168,f47])).

fof(f168,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f166,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f166,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(resolution,[],[f149,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f1144,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f381,f44])).

fof(f381,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),X0)
      | r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f371,f47])).

fof(f371,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),X0)
      | r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f364,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f364,plain,
    ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f363,f147])).

fof(f147,plain,
    ( v3_pre_topc(sK1,sK0)
    | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f142,f140])).

fof(f142,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f114,f38])).

fof(f38,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f363,plain,
    ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f362,f69])).

fof(f362,plain,
    ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f359,f44])).

fof(f359,plain,
    ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f320,f41])).

fof(f320,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f317,f176])).

fof(f176,plain,
    ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f147,f42])).

fof(f317,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK1,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK1,sK0,sK2)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f183,f177])).

fof(f177,plain,
    ( r2_hidden(sK2,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f147,f43])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f182,f45])).

fof(f182,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f181,f44])).

fof(f181,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f180,f47])).

fof(f180,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f178,f46])).

fof(f178,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(resolution,[],[f147,f55])).

fof(f1174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(X0))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f895,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f895,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f894,f140])).

fof(f894,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f893,f45])).

fof(f893,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f892,f44])).

fof(f892,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f891,f47])).

fof(f891,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f889,f46])).

fof(f889,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f618,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f618,plain,
    ( m1_connsp_2(sK1,sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f617,f140])).

fof(f617,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | m1_connsp_2(sK1,sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f610])).

fof(f610,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | m1_connsp_2(sK1,sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f306,f114])).

fof(f306,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f305,f45])).

fof(f305,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f304,f44])).

fof(f304,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f303,f47])).

fof(f303,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f301,f46])).

fof(f301,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0) ) ),
    inference(resolution,[],[f196,f55])).

fof(f196,plain,
    ( v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f195,f147])).

fof(f195,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f194,f140])).

fof(f194,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f193,f45])).

fof(f193,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f192,f47])).

fof(f192,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f190,f46])).

fof(f190,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f148,f58])).

fof(f148,plain,
    ( m1_connsp_2(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f143,f140])).

fof(f143,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | m1_connsp_2(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f114,f39])).

fof(f39,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f90,f46])).

fof(f90,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f80,f47])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f44,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f2820,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f2819,f69])).

fof(f2819,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f2816,f44])).

fof(f2816,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f2815,f41])).

fof(f2815,plain,(
    m1_connsp_2(sK1,sK0,sK2) ),
    inference(subsumption_resolution,[],[f2814,f2797])).

fof(f2797,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f42,f2335])).

fof(f2814,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f2789,f2800])).

fof(f2800,plain,(
    r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f2335,f43])).

fof(f2789,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f2338,f2329])).

fof(f2338,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0) ) ),
    inference(backward_demodulation,[],[f106,f2329])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
      | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f104,f92])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
      | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f103,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
      | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f101,f46])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
      | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0) ) ),
    inference(resolution,[],[f91,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:49:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (20573)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.49  % (20577)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (20587)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (20583)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (20592)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (20594)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (20579)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (20584)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (20595)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (20575)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (20582)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (20580)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (20579)Refutation not found, incomplete strategy% (20579)------------------------------
% 0.22/0.51  % (20579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20579)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20579)Memory used [KB]: 10618
% 0.22/0.51  % (20579)Time elapsed: 0.071 s
% 0.22/0.51  % (20579)------------------------------
% 0.22/0.51  % (20579)------------------------------
% 0.22/0.51  % (20586)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (20574)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (20578)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (20580)Refutation not found, incomplete strategy% (20580)------------------------------
% 0.22/0.52  % (20580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20580)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20580)Memory used [KB]: 1918
% 0.22/0.52  % (20580)Time elapsed: 0.102 s
% 0.22/0.52  % (20580)------------------------------
% 0.22/0.52  % (20580)------------------------------
% 0.22/0.52  % (20591)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (20581)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (20590)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (20585)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (20589)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (20596)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (20597)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (20593)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (20576)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (20588)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (20598)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.22/0.68  % (20582)Refutation not found, incomplete strategy% (20582)------------------------------
% 2.22/0.68  % (20582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (20582)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (20582)Memory used [KB]: 6140
% 2.22/0.68  % (20582)Time elapsed: 0.265 s
% 2.22/0.68  % (20582)------------------------------
% 2.22/0.68  % (20582)------------------------------
% 2.22/0.71  % (20578)Refutation found. Thanks to Tanya!
% 2.22/0.71  % SZS status Theorem for theBenchmark
% 2.22/0.71  % SZS output start Proof for theBenchmark
% 2.22/0.71  fof(f2821,plain,(
% 2.22/0.71    $false),
% 2.22/0.71    inference(subsumption_resolution,[],[f2820,f2335])).
% 2.22/0.71  fof(f2335,plain,(
% 2.22/0.71    v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(backward_demodulation,[],[f91,f2329])).
% 2.22/0.71  fof(f2329,plain,(
% 2.22/0.71    sK1 = k1_tops_1(sK0,sK1)),
% 2.22/0.71    inference(resolution,[],[f2313,f99])).
% 2.22/0.71  fof(f99,plain,(
% 2.22/0.71    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 2.22/0.71    inference(resolution,[],[f89,f67])).
% 2.22/0.71  fof(f67,plain,(
% 2.22/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.22/0.71    inference(cnf_transformation,[],[f1])).
% 2.22/0.71  fof(f1,axiom,(
% 2.22/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.22/0.71  fof(f89,plain,(
% 2.22/0.71    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.22/0.71    inference(subsumption_resolution,[],[f79,f47])).
% 2.22/0.71  fof(f47,plain,(
% 2.22/0.71    l1_pre_topc(sK0)),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f17,plain,(
% 2.22/0.71    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.71    inference(flattening,[],[f16])).
% 2.22/0.71  fof(f16,plain,(
% 2.22/0.71    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.22/0.71    inference(ennf_transformation,[],[f15])).
% 2.22/0.71  fof(f15,negated_conjecture,(
% 2.22/0.71    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.22/0.71    inference(negated_conjecture,[],[f14])).
% 2.22/0.71  fof(f14,conjecture,(
% 2.22/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.22/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 2.22/0.71  fof(f79,plain,(
% 2.22/0.71    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.22/0.71    inference(resolution,[],[f44,f54])).
% 2.22/0.71  fof(f54,plain,(
% 2.22/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f22])).
% 2.22/0.71  fof(f22,plain,(
% 2.22/0.71    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.71    inference(ennf_transformation,[],[f8])).
% 2.22/0.71  fof(f8,axiom,(
% 2.22/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.22/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.22/0.71  fof(f44,plain,(
% 2.22/0.71    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f2313,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(subsumption_resolution,[],[f2312,f44])).
% 2.22/0.71  fof(f2312,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.71    inference(subsumption_resolution,[],[f2311,f92])).
% 2.22/0.71  fof(f92,plain,(
% 2.22/0.71    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.71    inference(subsumption_resolution,[],[f81,f47])).
% 2.22/0.71  fof(f81,plain,(
% 2.22/0.71    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.71    inference(resolution,[],[f44,f64])).
% 2.22/0.71  fof(f64,plain,(
% 2.22/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.22/0.71    inference(cnf_transformation,[],[f37])).
% 2.22/0.71  fof(f37,plain,(
% 2.22/0.71    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.22/0.71    inference(flattening,[],[f36])).
% 2.22/0.71  fof(f36,plain,(
% 2.22/0.71    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.22/0.71    inference(ennf_transformation,[],[f6])).
% 2.22/0.71  fof(f6,axiom,(
% 2.22/0.71    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.22/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 2.22/0.71  fof(f2311,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.71    inference(duplicate_literal_removal,[],[f2306])).
% 2.22/0.71  fof(f2306,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(resolution,[],[f1880,f52])).
% 2.22/0.71  fof(f52,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f19])).
% 2.22/0.71  fof(f19,plain,(
% 2.22/0.71    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.71    inference(flattening,[],[f18])).
% 2.22/0.71  fof(f18,plain,(
% 2.22/0.71    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.71    inference(ennf_transformation,[],[f3])).
% 2.22/0.71  fof(f3,axiom,(
% 2.22/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.22/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 2.22/0.71  fof(f1880,plain,(
% 2.22/0.71    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(duplicate_literal_removal,[],[f1879])).
% 2.22/0.71  fof(f1879,plain,(
% 2.22/0.71    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(resolution,[],[f1174,f1185])).
% 2.22/0.71  fof(f1185,plain,(
% 2.22/0.71    m1_subset_1(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(k1_tops_1(sK0,sK1))) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(resolution,[],[f1168,f48])).
% 2.22/0.71  fof(f48,plain,(
% 2.22/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.22/0.71    inference(cnf_transformation,[],[f4])).
% 2.22/0.71  fof(f4,axiom,(
% 2.22/0.71    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.22/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.22/0.71  fof(f1168,plain,(
% 2.22/0.71    r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(subsumption_resolution,[],[f1144,f298])).
% 2.22/0.71  fof(f298,plain,(
% 2.22/0.71    r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(subsumption_resolution,[],[f297,f149])).
% 2.22/0.71  fof(f149,plain,(
% 2.22/0.71    v3_pre_topc(sK1,sK0) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(subsumption_resolution,[],[f144,f140])).
% 2.22/0.71  fof(f140,plain,(
% 2.22/0.71    m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(resolution,[],[f85,f92])).
% 2.22/0.71  fof(f85,plain,(
% 2.22/0.71    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK4(u1_struct_0(sK0),sK1,X1),u1_struct_0(sK0)) | r1_tarski(sK1,X1)) )),
% 2.22/0.71    inference(resolution,[],[f44,f50])).
% 2.22/0.71  fof(f50,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f19])).
% 2.22/0.71  fof(f144,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(resolution,[],[f114,f40])).
% 2.22/0.71  fof(f40,plain,(
% 2.22/0.71    ( ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | v3_pre_topc(sK1,sK0)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f114,plain,(
% 2.22/0.71    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(resolution,[],[f92,f86])).
% 2.22/0.71  fof(f86,plain,(
% 2.22/0.71    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X2),sK1) | r1_tarski(sK1,X2)) )),
% 2.22/0.71    inference(resolution,[],[f44,f51])).
% 2.22/0.71  fof(f51,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f19])).
% 2.22/0.71  fof(f297,plain,(
% 2.22/0.71    r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(subsumption_resolution,[],[f296,f69])).
% 2.22/0.71  fof(f69,plain,(
% 2.22/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.71    inference(equality_resolution,[],[f65])).
% 2.22/0.71  fof(f65,plain,(
% 2.22/0.71    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.22/0.71    inference(cnf_transformation,[],[f1])).
% 2.22/0.71  fof(f296,plain,(
% 2.22/0.71    r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(subsumption_resolution,[],[f293,f44])).
% 2.22/0.71  fof(f293,plain,(
% 2.22/0.71    r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(resolution,[],[f292,f41])).
% 2.22/0.71  fof(f41,plain,(
% 2.22/0.71    ( ! [X3] : (~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f292,plain,(
% 2.22/0.71    m1_connsp_2(sK1,sK0,sK2) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(subsumption_resolution,[],[f287,f164])).
% 2.22/0.71  fof(f164,plain,(
% 2.22/0.71    m1_subset_1(sK2,u1_struct_0(sK0)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)),
% 2.22/0.71    inference(resolution,[],[f149,f42])).
% 2.22/0.71  fof(f42,plain,(
% 2.22/0.71    ~v3_pre_topc(sK1,sK0) | m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f287,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | m1_connsp_2(sK1,sK0,sK2)),
% 2.22/0.71    inference(duplicate_literal_removal,[],[f286])).
% 2.22/0.71  fof(f286,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | m1_connsp_2(sK1,sK0,sK2) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)),
% 2.22/0.71    inference(resolution,[],[f171,f165])).
% 2.22/0.71  fof(f165,plain,(
% 2.22/0.71    r2_hidden(sK2,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)),
% 2.22/0.71    inference(resolution,[],[f149,f43])).
% 2.22/0.71  fof(f43,plain,(
% 2.22/0.71    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1)),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f171,plain,(
% 2.22/0.71    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f170,f45])).
% 2.22/0.71  fof(f45,plain,(
% 2.22/0.71    ~v2_struct_0(sK0)),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f170,plain,(
% 2.22/0.71    ( ! [X0] : (r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f169,f44])).
% 2.22/0.71  fof(f169,plain,(
% 2.22/0.71    ( ! [X0] : (r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f168,f47])).
% 2.22/0.71  fof(f168,plain,(
% 2.22/0.71    ( ! [X0] : (r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f166,f46])).
% 2.22/0.71  fof(f46,plain,(
% 2.22/0.71    v2_pre_topc(sK0)),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f166,plain,(
% 2.22/0.71    ( ! [X0] : (r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(resolution,[],[f149,f55])).
% 2.22/0.71  fof(f55,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f24])).
% 2.22/0.71  fof(f24,plain,(
% 2.22/0.71    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.71    inference(flattening,[],[f23])).
% 2.22/0.71  fof(f23,plain,(
% 2.22/0.71    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.71    inference(ennf_transformation,[],[f12])).
% 2.22/0.71  fof(f12,axiom,(
% 2.22/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.22/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 2.22/0.71  fof(f1144,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(resolution,[],[f381,f44])).
% 2.22/0.71  fof(f381,plain,(
% 2.22/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),X0) | r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,X0))) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f371,f47])).
% 2.22/0.71  fof(f371,plain,(
% 2.22/0.71    ( ! [X0] : (r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),X0) | r1_tarski(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,X0))) )),
% 2.22/0.71    inference(resolution,[],[f364,f53])).
% 2.22/0.71  fof(f53,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 2.22/0.71    inference(cnf_transformation,[],[f21])).
% 2.22/0.71  fof(f21,plain,(
% 2.22/0.71    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.71    inference(flattening,[],[f20])).
% 2.22/0.71  fof(f20,plain,(
% 2.22/0.71    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.71    inference(ennf_transformation,[],[f9])).
% 2.22/0.71  fof(f9,axiom,(
% 2.22/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.22/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 2.22/0.71  fof(f364,plain,(
% 2.22/0.71    m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(subsumption_resolution,[],[f363,f147])).
% 2.22/0.71  fof(f147,plain,(
% 2.22/0.71    v3_pre_topc(sK1,sK0) | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(subsumption_resolution,[],[f142,f140])).
% 2.22/0.71  fof(f142,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(resolution,[],[f114,f38])).
% 2.22/0.71  fof(f38,plain,(
% 2.22/0.71    ( ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f17])).
% 2.22/0.71  fof(f363,plain,(
% 2.22/0.71    m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(subsumption_resolution,[],[f362,f69])).
% 2.22/0.71  fof(f362,plain,(
% 2.22/0.71    m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(subsumption_resolution,[],[f359,f44])).
% 2.22/0.71  fof(f359,plain,(
% 2.22/0.71    m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.22/0.71    inference(resolution,[],[f320,f41])).
% 2.22/0.71  fof(f320,plain,(
% 2.22/0.71    m1_connsp_2(sK1,sK0,sK2) | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.71    inference(subsumption_resolution,[],[f317,f176])).
% 2.22/0.71  fof(f176,plain,(
% 2.22/0.71    m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.22/0.71    inference(resolution,[],[f147,f42])).
% 2.22/0.71  fof(f317,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK1,sK0,sK2)),
% 2.22/0.71    inference(duplicate_literal_removal,[],[f314])).
% 2.22/0.71  fof(f314,plain,(
% 2.22/0.71    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK1,sK0,sK2) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.71    inference(resolution,[],[f183,f177])).
% 2.22/0.71  fof(f177,plain,(
% 2.22/0.71    r2_hidden(sK2,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.71    inference(resolution,[],[f147,f43])).
% 2.22/0.71  fof(f183,plain,(
% 2.22/0.71    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f182,f45])).
% 2.22/0.71  fof(f182,plain,(
% 2.22/0.71    ( ! [X0] : (m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f181,f44])).
% 2.22/0.71  fof(f181,plain,(
% 2.22/0.71    ( ! [X0] : (m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f180,f47])).
% 2.22/0.71  fof(f180,plain,(
% 2.22/0.71    ( ! [X0] : (m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(subsumption_resolution,[],[f178,f46])).
% 2.22/0.71  fof(f178,plain,(
% 2.22/0.71    ( ! [X0] : (m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.71    inference(resolution,[],[f147,f55])).
% 2.22/0.72  fof(f1174,plain,(
% 2.22/0.72    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(X0)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),X0)) )),
% 2.22/0.72    inference(resolution,[],[f895,f60])).
% 2.22/0.72  fof(f60,plain,(
% 2.22/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f31])).
% 2.22/0.72  fof(f31,plain,(
% 2.22/0.72    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.72    inference(ennf_transformation,[],[f2])).
% 2.22/0.72  fof(f2,axiom,(
% 2.22/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.22/0.72  fof(f895,plain,(
% 2.22/0.72    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 2.22/0.72    inference(subsumption_resolution,[],[f894,f140])).
% 2.22/0.72  fof(f894,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 2.22/0.72    inference(subsumption_resolution,[],[f893,f45])).
% 2.22/0.72  fof(f893,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | v2_struct_0(sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f892,f44])).
% 2.22/0.72  fof(f892,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | v2_struct_0(sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f891,f47])).
% 2.22/0.72  fof(f891,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | v2_struct_0(sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f889,f46])).
% 2.22/0.72  fof(f889,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | v2_struct_0(sK0)),
% 2.22/0.72    inference(resolution,[],[f618,f58])).
% 2.22/0.72  fof(f58,plain,(
% 2.22/0.72    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | v2_struct_0(X0)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f28])).
% 2.22/0.72  fof(f28,plain,(
% 2.22/0.72    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.72    inference(flattening,[],[f27])).
% 2.22/0.72  fof(f27,plain,(
% 2.22/0.72    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.72    inference(ennf_transformation,[],[f11])).
% 2.22/0.72  fof(f11,axiom,(
% 2.22/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 2.22/0.72  fof(f618,plain,(
% 2.22/0.72    m1_connsp_2(sK1,sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))),
% 2.22/0.72    inference(subsumption_resolution,[],[f617,f140])).
% 2.22/0.72  fof(f617,plain,(
% 2.22/0.72    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),
% 2.22/0.72    inference(duplicate_literal_removal,[],[f610])).
% 2.22/0.72  fof(f610,plain,(
% 2.22/0.72    r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.72    inference(resolution,[],[f306,f114])).
% 2.22/0.72  fof(f306,plain,(
% 2.22/0.72    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.72    inference(subsumption_resolution,[],[f305,f45])).
% 2.22/0.72  fof(f305,plain,(
% 2.22/0.72    ( ! [X0] : (r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.72    inference(subsumption_resolution,[],[f304,f44])).
% 2.22/0.72  fof(f304,plain,(
% 2.22/0.72    ( ! [X0] : (r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.72    inference(subsumption_resolution,[],[f303,f47])).
% 2.22/0.72  fof(f303,plain,(
% 2.22/0.72    ( ! [X0] : (r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.72    inference(subsumption_resolution,[],[f301,f46])).
% 2.22/0.72  fof(f301,plain,(
% 2.22/0.72    ( ! [X0] : (r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0)) )),
% 2.22/0.72    inference(resolution,[],[f196,f55])).
% 2.22/0.72  fof(f196,plain,(
% 2.22/0.72    v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))),
% 2.22/0.72    inference(subsumption_resolution,[],[f195,f147])).
% 2.22/0.72  fof(f195,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))),
% 2.22/0.72    inference(subsumption_resolution,[],[f194,f140])).
% 2.22/0.72  fof(f194,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))),
% 2.22/0.72    inference(subsumption_resolution,[],[f193,f45])).
% 2.22/0.72  fof(f193,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | v2_struct_0(sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f192,f47])).
% 2.22/0.72  fof(f192,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | v2_struct_0(sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f190,f46])).
% 2.22/0.72  fof(f190,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | v2_struct_0(sK0)),
% 2.22/0.72    inference(resolution,[],[f148,f58])).
% 2.22/0.72  fof(f148,plain,(
% 2.22/0.72    m1_connsp_2(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f143,f140])).
% 2.22/0.72  fof(f143,plain,(
% 2.22/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | m1_connsp_2(sK3(sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK0,sK4(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) | v3_pre_topc(sK1,sK0)),
% 2.22/0.72    inference(resolution,[],[f114,f39])).
% 2.22/0.72  fof(f39,plain,(
% 2.22/0.72    ( ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | v3_pre_topc(sK1,sK0)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f17])).
% 2.22/0.72  fof(f91,plain,(
% 2.22/0.72    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f90,f46])).
% 2.22/0.72  fof(f90,plain,(
% 2.22/0.72    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f80,f47])).
% 2.22/0.72  fof(f80,plain,(
% 2.22/0.72    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.22/0.72    inference(resolution,[],[f44,f61])).
% 2.22/0.72  fof(f61,plain,(
% 2.22/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f33])).
% 2.22/0.72  fof(f33,plain,(
% 2.22/0.72    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.22/0.72    inference(flattening,[],[f32])).
% 2.22/0.72  fof(f32,plain,(
% 2.22/0.72    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.22/0.72    inference(ennf_transformation,[],[f7])).
% 2.22/0.72  fof(f7,axiom,(
% 2.22/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.22/0.72  fof(f2820,plain,(
% 2.22/0.72    ~v3_pre_topc(sK1,sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f2819,f69])).
% 2.22/0.72  fof(f2819,plain,(
% 2.22/0.72    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.22/0.72    inference(subsumption_resolution,[],[f2816,f44])).
% 2.22/0.72  fof(f2816,plain,(
% 2.22/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.22/0.72    inference(resolution,[],[f2815,f41])).
% 2.22/0.72  fof(f2815,plain,(
% 2.22/0.72    m1_connsp_2(sK1,sK0,sK2)),
% 2.22/0.72    inference(subsumption_resolution,[],[f2814,f2797])).
% 2.22/0.72  fof(f2797,plain,(
% 2.22/0.72    m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.22/0.72    inference(global_subsumption,[],[f42,f2335])).
% 2.22/0.72  fof(f2814,plain,(
% 2.22/0.72    m1_connsp_2(sK1,sK0,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.22/0.72    inference(resolution,[],[f2789,f2800])).
% 2.22/0.72  fof(f2800,plain,(
% 2.22/0.72    r2_hidden(sK2,sK1)),
% 2.22/0.72    inference(resolution,[],[f2335,f43])).
% 2.22/0.72  fof(f2789,plain,(
% 2.22/0.72    ( ! [X0] : (~r2_hidden(X0,sK1) | m1_connsp_2(sK1,sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.22/0.72    inference(forward_demodulation,[],[f2338,f2329])).
% 2.22/0.72  fof(f2338,plain,(
% 2.22/0.72    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0)) )),
% 2.22/0.72    inference(backward_demodulation,[],[f106,f2329])).
% 2.22/0.72  fof(f106,plain,(
% 2.22/0.72    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0)) )),
% 2.22/0.72    inference(subsumption_resolution,[],[f105,f45])).
% 2.22/0.72  fof(f105,plain,(
% 2.22/0.72    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK1)) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0)) )),
% 2.22/0.72    inference(subsumption_resolution,[],[f104,f92])).
% 2.22/0.72  fof(f104,plain,(
% 2.22/0.72    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK1)) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0)) )),
% 2.22/0.72    inference(subsumption_resolution,[],[f103,f47])).
% 2.22/0.72  fof(f103,plain,(
% 2.22/0.72    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK1)) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0)) )),
% 2.22/0.72    inference(subsumption_resolution,[],[f101,f46])).
% 2.22/0.72  fof(f101,plain,(
% 2.22/0.72    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK1)) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,X0)) )),
% 2.22/0.72    inference(resolution,[],[f91,f55])).
% 2.22/0.72  % SZS output end Proof for theBenchmark
% 2.22/0.72  % (20578)------------------------------
% 2.22/0.72  % (20578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.72  % (20578)Termination reason: Refutation
% 2.22/0.72  
% 2.22/0.72  % (20578)Memory used [KB]: 7931
% 2.22/0.72  % (20578)Time elapsed: 0.289 s
% 2.22/0.72  % (20578)------------------------------
% 2.22/0.72  % (20578)------------------------------
% 2.22/0.72  % (20572)Success in time 0.348 s
%------------------------------------------------------------------------------
