%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 170 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  179 ( 606 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(subsumption_resolution,[],[f123,f120])).

fof(f120,plain,(
    ! [X6,X7] : sK3(u1_orders_2(sK0)) != k4_tarski(X6,X7) ),
    inference(subsumption_resolution,[],[f119,f73])).

fof(f73,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f72,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_orders_2(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(f72,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f71,f29])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f26,plain,(
    ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f119,plain,(
    ! [X6,X7] :
      ( sK3(u1_orders_2(sK0)) != k4_tarski(X6,X7)
      | r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f116,f25])).

fof(f116,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | sK3(u1_orders_2(sK0)) != k4_tarski(X3,X4)
      | r2_hidden(k4_tarski(X2,X2),u1_orders_2(sK0)) ) ),
    inference(subsumption_resolution,[],[f111,f60])).

fof(f60,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f59,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f58,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f58,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f111,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(k4_tarski(X2,X2),u1_orders_2(sK0))
      | sK3(u1_orders_2(sK0)) != k4_tarski(X3,X4)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f90,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f90,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X1,X1),u1_orders_2(sK0))
      | k4_tarski(X2,X3) != sK3(u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f75,f42])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(u1_orders_2(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f52,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(f52,plain,(
    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f51,f29])).

fof(f51,plain,
    ( ~ l1_orders_2(sK0)
    | r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f123,plain,(
    sK3(u1_orders_2(sK0)) = k4_tarski(sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),sK7(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f102,f57])).

fof(f57,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK3(u1_orders_2(sK0)) = k4_tarski(sK6(sK3(u1_orders_2(sK0)),X0,X1),sK7(sK3(u1_orders_2(sK0)),X0,X1)) ) ),
    inference(resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,X3)
      | k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f101,plain,(
    r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f100,f73])).

fof(f100,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0))
    | r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(resolution,[],[f97,f25])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) ) ),
    inference(subsumption_resolution,[],[f92,f60])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))
      | r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f89,f46])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))
      | r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f75,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:03:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (24862)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.45  % (24862)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f127,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f123,f120])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    ( ! [X6,X7] : (sK3(u1_orders_2(sK0)) != k4_tarski(X6,X7)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f119,f73])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    ~r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f72,f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~r1_orders_2(X0,X1,X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~r1_orders_2(X0,X1,X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.45    inference(negated_conjecture,[],[f10])).
% 0.22/0.45  fof(f10,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f71,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    l1_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f70])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))),
% 0.22/0.45    inference(resolution,[],[f26,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ~r1_orders_2(sK0,sK1,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f119,plain,(
% 0.22/0.45    ( ! [X6,X7] : (sK3(u1_orders_2(sK0)) != k4_tarski(X6,X7) | r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))) )),
% 0.22/0.45    inference(resolution,[],[f116,f25])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    ( ! [X4,X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK3(u1_orders_2(sK0)) != k4_tarski(X3,X4) | r2_hidden(k4_tarski(X2,X2),u1_orders_2(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f111,f60])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f59,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ~v2_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    v2_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.45    inference(resolution,[],[f58,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    l1_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f29,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.45  fof(f111,plain,(
% 0.22/0.45    ( ! [X4,X2,X3] : (r2_hidden(k4_tarski(X2,X2),u1_orders_2(sK0)) | sK3(u1_orders_2(sK0)) != k4_tarski(X3,X4) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.45    inference(resolution,[],[f90,f46])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    ( ! [X2,X3,X1] : (~r2_hidden(X1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(X1,X1),u1_orders_2(sK0)) | k4_tarski(X2,X3) != sK3(u1_orders_2(sK0))) )),
% 0.22/0.45    inference(resolution,[],[f75,f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_relat_1(u1_orders_2(sK0)) | ~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))) )),
% 0.22/0.45    inference(resolution,[],[f52,f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X2,X1) | r2_hidden(k4_tarski(X2,X2),X0) | ~r1_relat_2(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f51,f29])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    ~l1_orders_2(sK0) | r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.22/0.45    inference(resolution,[],[f28,f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ( ! [X0] : (~l1_orders_2(X0) | r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v3_orders_2(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0] : ((v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0] : (l1_orders_2(X0) => (v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    v3_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f123,plain,(
% 0.22/0.45    sK3(u1_orders_2(sK0)) = k4_tarski(sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),sK7(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.22/0.45    inference(resolution,[],[f102,f57])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.45    inference(resolution,[],[f29,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.45  fof(f102,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK3(u1_orders_2(sK0)) = k4_tarski(sK6(sK3(u1_orders_2(sK0)),X0,X1),sK7(sK3(u1_orders_2(sK0)),X0,X1))) )),
% 0.22/0.45    inference(resolution,[],[f101,f47])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,X3) | k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.45    inference(flattening,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.22/0.45  fof(f101,plain,(
% 0.22/0.45    r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f100,f73])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0)) | r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))),
% 0.22/0.45    inference(resolution,[],[f97,f25])).
% 0.22/0.45  fof(f97,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0)) | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f92,f60])).
% 0.22/0.45  fof(f92,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) | r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.45    inference(resolution,[],[f89,f46])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) | r2_hidden(sK3(u1_orders_2(sK0)),u1_orders_2(sK0))) )),
% 0.22/0.45    inference(resolution,[],[f75,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f21])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (24862)------------------------------
% 0.22/0.45  % (24862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (24862)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (24862)Memory used [KB]: 1663
% 0.22/0.45  % (24862)Time elapsed: 0.006 s
% 0.22/0.45  % (24862)------------------------------
% 0.22/0.45  % (24862)------------------------------
% 0.22/0.45  % (24848)Success in time 0.092 s
%------------------------------------------------------------------------------
