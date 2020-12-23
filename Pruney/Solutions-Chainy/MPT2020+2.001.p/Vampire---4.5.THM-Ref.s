%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 791 expanded)
%              Number of leaves         :    7 ( 148 expanded)
%              Depth                    :   31
%              Number of atoms          :  243 (3978 expanded)
%              Number of equality atoms :   18 ( 788 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(subsumption_resolution,[],[f132,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v1_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v1_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v1_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v1_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).

fof(f132,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f131,f98])).

fof(f98,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f97,f93])).

fof(f93,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f26,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f89,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f89,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f82,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f64,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(superposition,[],[f37,f21])).

fof(f21,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f64,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f63,f27])).

fof(f63,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f97,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(resolution,[],[f81,f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f81,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f79,f27])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f76,f40])).

fof(f76,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f75,f26])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f71,f27])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f53,f21])).

fof(f53,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f52,f26])).

fof(f52,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f26,f39])).

fof(f131,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f44,plain,(
    ~ v1_tops_2(sK2,sK1) ),
    inference(backward_demodulation,[],[f24,f22])).

fof(f22,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ~ v1_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f130,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v1_tops_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f128,f26])).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | v1_tops_2(sK2,sK1) ),
    inference(resolution,[],[f127,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f127,plain,(
    v3_pre_topc(sK4(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f126,f76])).

fof(f126,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(sK4(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f125,f102])).

fof(f102,plain,(
    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f58,f98])).

fof(f58,plain,(
    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f57,f44])).

fof(f57,plain,
    ( m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f55,f26])).

fof(f55,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_2(sK2,sK1) ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f20,f22])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f125,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(sK4(sK1,sK2),sK1) ),
    inference(superposition,[],[f122,f98])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | v3_pre_topc(sK4(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f121,f27])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK4(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f120,f102])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK4(sK1,sK2),X0) ) ),
    inference(resolution,[],[f119,f43])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f119,plain,(
    v3_pre_topc(sK4(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f118,f25])).

fof(f118,plain,
    ( v3_pre_topc(sK4(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f117,f27])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(sK4(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f116,f102])).

fof(f116,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_pre_topc(sK4(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f69,f23])).

fof(f23,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_tops_2(sK2,X0)
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(sK4(sK1,sK2),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f60,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    r2_hidden(sK4(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f59,f44])).

fof(f59,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | v1_tops_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f56,f26])).

fof(f56,plain,
    ( ~ l1_pre_topc(sK1)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v1_tops_2(sK2,sK1) ),
    inference(resolution,[],[f45,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:13:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (3638)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (3643)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (3644)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (3633)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (3638)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (3644)Refutation not found, incomplete strategy% (3644)------------------------------
% 0.22/0.54  % (3644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3642)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.55  % (3637)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (3646)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (3636)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.55  % (3644)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3644)Memory used [KB]: 10618
% 0.22/0.55  % (3644)Time elapsed: 0.110 s
% 0.22/0.55  % (3644)------------------------------
% 0.22/0.55  % (3644)------------------------------
% 0.22/0.56  % (3635)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (3653)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f132,f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v1_tops_2(X3,X1) & (v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tops_2(X3,X1))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f8])).
% 0.22/0.56  fof(f8,conjecture,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tops_2(X3,X1))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).
% 0.22/0.56  fof(f132,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.56    inference(forward_demodulation,[],[f131,f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f97,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f91,f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    l1_pre_topc(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.56    inference(resolution,[],[f89,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    m1_pre_topc(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f82,f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f64,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f65,f26])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 0.22/0.56    inference(superposition,[],[f37,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f63,f27])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(resolution,[],[f47,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    m1_pre_topc(sK0,sK0)),
% 0.22/0.56    inference(resolution,[],[f27,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f81,f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f79,f27])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f76,f40])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    m1_pre_topc(sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f75,f26])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f71,f27])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f54,f37])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.56    inference(forward_demodulation,[],[f53,f21])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f52,f26])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.56    inference(resolution,[],[f46,f38])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    m1_pre_topc(sK1,sK1)),
% 0.22/0.56    inference(resolution,[],[f26,f39])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f130,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ~v1_tops_2(sK2,sK1)),
% 0.22/0.56    inference(backward_demodulation,[],[f24,f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    sK2 = sK3),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ~v1_tops_2(sK3,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | v1_tops_2(sK2,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f128,f26])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | v1_tops_2(sK2,sK1)),
% 0.22/0.56    inference(resolution,[],[f127,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v3_pre_topc(sK4(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v1_tops_2(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    v3_pre_topc(sK4(sK1,sK2),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f126,f76])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ~m1_pre_topc(sK1,sK0) | v3_pre_topc(sK4(sK1,sK2),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f125,f102])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f58,f98])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f57,f44])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_tops_2(sK2,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f55,f26])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_tops_2(sK2,sK1)),
% 0.22/0.56    inference(resolution,[],[f45,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.56    inference(forward_demodulation,[],[f20,f22])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | v3_pre_topc(sK4(sK1,sK2),sK1)),
% 0.22/0.56    inference(superposition,[],[f122,f98])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | v3_pre_topc(sK4(sK1,sK2),X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f121,f27])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK4(sK1,sK2),X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f120,f102])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK4(sK1,sK2),X0)) )),
% 0.22/0.56    inference(resolution,[],[f119,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X2,X0,X3] : (~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 0.22/0.56    inference(equality_resolution,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    v3_pre_topc(sK4(sK1,sK2),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f118,f25])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    v3_pre_topc(sK4(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f117,f27])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | v3_pre_topc(sK4(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f116,f102])).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(sK4(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.56    inference(resolution,[],[f69,f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    v1_tops_2(sK2,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_tops_2(sK2,X0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(sK4(sK1,sK2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.22/0.56    inference(resolution,[],[f60,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    r2_hidden(sK4(sK1,sK2),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f59,f44])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    r2_hidden(sK4(sK1,sK2),sK2) | v1_tops_2(sK2,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f56,f26])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | r2_hidden(sK4(sK1,sK2),sK2) | v1_tops_2(sK2,sK1)),
% 0.22/0.56    inference(resolution,[],[f45,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1),X1) | v1_tops_2(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (3638)------------------------------
% 0.22/0.56  % (3638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (3638)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (3638)Memory used [KB]: 6140
% 0.22/0.56  % (3638)Time elapsed: 0.113 s
% 0.22/0.56  % (3638)------------------------------
% 0.22/0.56  % (3638)------------------------------
% 0.22/0.56  % (3634)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (3632)Success in time 0.199 s
%------------------------------------------------------------------------------
