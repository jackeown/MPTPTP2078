%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 (1128 expanded)
%              Number of leaves         :   10 ( 218 expanded)
%              Depth                    :   23
%              Number of atoms          :  238 (5546 expanded)
%              Number of equality atoms :   25 ( 628 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(subsumption_resolution,[],[f254,f98])).

fof(f98,plain,(
    k1_xboole_0 != sK2 ),
    inference(resolution,[],[f88,f26])).

fof(f26,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f88,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f84,f67])).

fof(f67,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f66,f53])).

fof(f53,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f48,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f65,f50])).

fof(f50,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f46,f30])).

fof(f46,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f65,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f27,f52])).

% (2355)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f52,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f51,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f47,f30])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f27,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(X2,sK0)
      | ~ r1_tarski(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f79,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | r1_tarski(k1_tops_1(sK0,sK1),X1) ) ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f254,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f252,f209])).

fof(f209,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_xboole_0)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f194,f33])).

fof(f33,plain,(
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

fof(f194,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f192,f169])).

fof(f169,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f165,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f165,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f123,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f123,plain,(
    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f93,f103])).

fof(f103,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f102,f30])).

fof(f102,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f101,f28])).

fof(f101,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f88,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f84,f42])).

fof(f192,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_tops_1(sK0,k1_xboole_0),X1)
      | r1_tarski(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f185,f39])).

fof(f185,plain,(
    r1_tarski(k1_xboole_0,k1_tops_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f181,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f181,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f132,f119])).

fof(f119,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f84,f103])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f122,f103])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) ) ),
    inference(backward_demodulation,[],[f87,f103])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f84,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f58,f30])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f252,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f251,f103])).

fof(f251,plain,(
    r1_tarski(sK2,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f247,f100])).

fof(f100,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f88,f24])).

fof(f24,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f247,plain,
    ( ~ r1_tarski(sK2,sK1)
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f144,f28])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f143,f30])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f142,f97])).

fof(f97,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f88,f23])).

fof(f23,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f99,f38])).

fof(f99,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f88,f25])).

fof(f25,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:30:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (2353)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (2344)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (2346)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (2347)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (2341)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (2354)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (2346)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (2342)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2357)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (2366)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (2362)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (2364)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f254,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    k1_xboole_0 != sK2),
% 0.21/0.51    inference(resolution,[],[f88,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ~v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    v2_tops_1(sK1,sK0)),
% 0.21/0.51    inference(resolution,[],[f84,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f66,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f48,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.21/0.51    inference(resolution,[],[f28,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f65,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f46,f30])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.21/0.51    inference(resolution,[],[f28,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.21/0.51    inference(resolution,[],[f27,f52])).
% 0.21/0.51  % (2355)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f51,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f47,f30])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.21/0.51    inference(resolution,[],[f28,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2] : (~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(resolution,[],[f79,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f62,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f28,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(sK1,X1) | r1_tarski(k1_tops_1(sK0,sK1),X1)) )),
% 0.21/0.51    inference(resolution,[],[f50,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    k1_xboole_0 = sK2),
% 0.21/0.51    inference(resolution,[],[f252,f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ( ! [X5] : (~r1_tarski(X5,k1_xboole_0) | k1_xboole_0 = X5) )),
% 0.21/0.51    inference(resolution,[],[f194,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f192,f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,k1_xboole_0),X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f165,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.51    inference(resolution,[],[f123,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f93,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f30])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f28])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f88,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f89,f30])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f84,f42])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(k1_tops_1(sK0,k1_xboole_0),X1) | r1_tarski(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f185,f39])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    r1_tarski(k1_xboole_0,k1_tops_1(sK0,k1_xboole_0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f181,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,k1_tops_1(sK0,k1_xboole_0))),
% 0.21/0.51    inference(resolution,[],[f132,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(backward_demodulation,[],[f84,f103])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f122,f103])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f87,f103])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(resolution,[],[f84,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f58,f30])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(resolution,[],[f52,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f251,f103])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_tops_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f247,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    r1_tarski(sK2,sK1)),
% 0.21/0.51    inference(resolution,[],[f88,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ~v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    ~r1_tarski(sK2,sK1) | r1_tarski(sK2,k1_tops_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f144,f28])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f30])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(resolution,[],[f88,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ~v2_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.21/0.51    inference(resolution,[],[f99,f38])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    v3_pre_topc(sK2,sK0)),
% 0.21/0.51    inference(resolution,[],[f88,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ~v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (2346)------------------------------
% 0.21/0.51  % (2346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2346)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (2346)Memory used [KB]: 6268
% 0.21/0.51  % (2346)Time elapsed: 0.102 s
% 0.21/0.51  % (2346)------------------------------
% 0.21/0.51  % (2346)------------------------------
% 0.21/0.51  % (2338)Success in time 0.15 s
%------------------------------------------------------------------------------
