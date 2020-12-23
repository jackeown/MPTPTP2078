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
% DateTime   : Thu Dec  3 13:10:50 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 353 expanded)
%              Number of leaves         :    9 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  186 (1105 expanded)
%              Number of equality atoms :   25 (  75 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1627,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1626,f1582])).

fof(f1582,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f62,f1580])).

fof(f1580,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1547,f61])).

fof(f61,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f1547,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f174,f1545])).

fof(f1545,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f598,f1544])).

fof(f1544,plain,(
    r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f1539,f877])).

fof(f877,plain,(
    r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f876,f63])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f876,plain,
    ( r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f871])).

fof(f871,plain,
    ( r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f493,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f493,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,sK1),sK1)
    | r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f163,f63])).

fof(f163,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X2),sK1)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f93,f63])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1539,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f374,f63])).

fof(f374,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f373,f123])).

fof(f123,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f87,f63])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f373,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) ) ),
    inference(superposition,[],[f95,f129])).

fof(f129,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f88,f63])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f598,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f586,f170])).

fof(f170,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f168,f106])).

fof(f106,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f72,f64])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f168,plain,
    ( ~ l1_struct_0(sK0)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f67,f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f586,plain,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f190,f123])).

fof(f190,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,X2)
      | ~ r1_xboole_0(sK1,X2)
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = X2 ) ),
    inference(subsumption_resolution,[],[f187,f106])).

fof(f187,plain,(
    ! [X2] :
      ( ~ l1_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,X2)
      | ~ r1_xboole_0(sK1,X2)
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = X2 ) ),
    inference(resolution,[],[f71,f63])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
      | ~ r1_xboole_0(X1,X2)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
              | ~ r1_xboole_0(X1,X2)
              | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
              | ~ r1_xboole_0(X1,X2)
              | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).

fof(f174,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f172,f64])).

fof(f172,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f76,f63])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f62,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f1626,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1625,f64])).

fof(f1625,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1624,f63])).

fof(f1624,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1623,f1580])).

fof(f1623,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f75,f1545])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:06:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (24187)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (24201)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (24204)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (24195)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (24196)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (24202)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (24188)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (24192)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (24193)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (24188)Refutation not found, incomplete strategy% (24188)------------------------------
% 0.22/0.50  % (24188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24188)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (24188)Memory used [KB]: 10618
% 0.22/0.50  % (24188)Time elapsed: 0.051 s
% 0.22/0.50  % (24188)------------------------------
% 0.22/0.50  % (24188)------------------------------
% 0.22/0.50  % (24194)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (24207)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (24191)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (24189)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (24203)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (24200)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (24199)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (24190)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (24197)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (24205)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (24207)Refutation not found, incomplete strategy% (24207)------------------------------
% 0.22/0.52  % (24207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24207)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (24207)Memory used [KB]: 10618
% 0.22/0.52  % (24207)Time elapsed: 0.105 s
% 0.22/0.52  % (24207)------------------------------
% 0.22/0.52  % (24207)------------------------------
% 1.42/0.54  % (24198)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.42/0.55  % (24206)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.53/0.59  % (24204)Refutation found. Thanks to Tanya!
% 1.53/0.59  % SZS status Theorem for theBenchmark
% 1.53/0.59  % SZS output start Proof for theBenchmark
% 1.53/0.59  fof(f1627,plain,(
% 1.53/0.59    $false),
% 1.53/0.59    inference(subsumption_resolution,[],[f1626,f1582])).
% 1.53/0.59  fof(f1582,plain,(
% 1.53/0.59    ~v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(subsumption_resolution,[],[f62,f1580])).
% 1.53/0.59  fof(f1580,plain,(
% 1.53/0.59    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.53/0.59    inference(subsumption_resolution,[],[f1547,f61])).
% 1.53/0.59  fof(f61,plain,(
% 1.53/0.59    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(cnf_transformation,[],[f30])).
% 1.53/0.59  fof(f30,plain,(
% 1.53/0.59    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.53/0.59    inference(ennf_transformation,[],[f29])).
% 1.53/0.59  fof(f29,negated_conjecture,(
% 1.53/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.53/0.59    inference(negated_conjecture,[],[f28])).
% 1.53/0.59  fof(f28,conjecture,(
% 1.53/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 1.53/0.59  fof(f1547,plain,(
% 1.53/0.59    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(backward_demodulation,[],[f174,f1545])).
% 1.53/0.59  fof(f1545,plain,(
% 1.53/0.59    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 1.53/0.59    inference(subsumption_resolution,[],[f598,f1544])).
% 1.53/0.59  fof(f1544,plain,(
% 1.53/0.59    r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.53/0.59    inference(subsumption_resolution,[],[f1539,f877])).
% 1.53/0.59  fof(f877,plain,(
% 1.53/0.59    r1_tarski(sK1,sK1)),
% 1.53/0.59    inference(subsumption_resolution,[],[f876,f63])).
% 1.53/0.59  fof(f63,plain,(
% 1.53/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.59    inference(cnf_transformation,[],[f30])).
% 1.53/0.59  fof(f876,plain,(
% 1.53/0.59    r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.59    inference(duplicate_literal_removal,[],[f871])).
% 1.53/0.59  fof(f871,plain,(
% 1.53/0.59    r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK1)),
% 1.53/0.59    inference(resolution,[],[f493,f94])).
% 1.53/0.59  fof(f94,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f52])).
% 1.53/0.59  fof(f52,plain,(
% 1.53/0.59    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.59    inference(flattening,[],[f51])).
% 1.53/0.59  fof(f51,plain,(
% 1.53/0.59    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.59    inference(ennf_transformation,[],[f11])).
% 1.53/0.59  fof(f11,axiom,(
% 1.53/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 1.53/0.59  fof(f493,plain,(
% 1.53/0.59    r2_hidden(sK4(u1_struct_0(sK0),sK1,sK1),sK1) | r1_tarski(sK1,sK1)),
% 1.53/0.59    inference(resolution,[],[f163,f63])).
% 1.53/0.59  fof(f163,plain,(
% 1.53/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X2),sK1) | r1_tarski(sK1,X2)) )),
% 1.53/0.59    inference(resolution,[],[f93,f63])).
% 1.53/0.59  fof(f93,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f52])).
% 1.53/0.59  fof(f1539,plain,(
% 1.53/0.59    ~r1_tarski(sK1,sK1) | r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.53/0.59    inference(resolution,[],[f374,f63])).
% 1.53/0.59  fof(f374,plain,(
% 1.53/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))) )),
% 1.53/0.59    inference(subsumption_resolution,[],[f373,f123])).
% 1.53/0.59  fof(f123,plain,(
% 1.53/0.59    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.59    inference(resolution,[],[f87,f63])).
% 1.53/0.59  fof(f87,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f46])).
% 1.53/0.59  fof(f46,plain,(
% 1.53/0.59    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.59    inference(ennf_transformation,[],[f2])).
% 1.53/0.59  fof(f2,axiom,(
% 1.53/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.53/0.59  fof(f373,plain,(
% 1.53/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))) )),
% 1.53/0.59    inference(superposition,[],[f95,f129])).
% 1.53/0.59  fof(f129,plain,(
% 1.53/0.59    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.53/0.59    inference(resolution,[],[f88,f63])).
% 1.53/0.59  fof(f88,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.53/0.59    inference(cnf_transformation,[],[f47])).
% 1.53/0.59  fof(f47,plain,(
% 1.53/0.59    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.59    inference(ennf_transformation,[],[f5])).
% 1.53/0.59  fof(f5,axiom,(
% 1.53/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.53/0.59  fof(f95,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_xboole_0(X1,X2)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f53])).
% 1.53/0.59  fof(f53,plain,(
% 1.53/0.59    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.59    inference(ennf_transformation,[],[f9])).
% 1.53/0.59  fof(f9,axiom,(
% 1.53/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 1.53/0.59  fof(f598,plain,(
% 1.53/0.59    ~r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 1.53/0.59    inference(subsumption_resolution,[],[f586,f170])).
% 1.53/0.59  fof(f170,plain,(
% 1.53/0.59    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.53/0.59    inference(subsumption_resolution,[],[f168,f106])).
% 1.53/0.59  fof(f106,plain,(
% 1.53/0.59    l1_struct_0(sK0)),
% 1.53/0.59    inference(resolution,[],[f72,f64])).
% 1.53/0.59  fof(f64,plain,(
% 1.53/0.59    l1_pre_topc(sK0)),
% 1.53/0.59    inference(cnf_transformation,[],[f30])).
% 1.53/0.59  fof(f72,plain,(
% 1.53/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f37])).
% 1.53/0.59  fof(f37,plain,(
% 1.53/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.53/0.59    inference(ennf_transformation,[],[f21])).
% 1.53/0.59  fof(f21,axiom,(
% 1.53/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.53/0.59  fof(f168,plain,(
% 1.53/0.59    ~l1_struct_0(sK0) | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.53/0.59    inference(resolution,[],[f67,f63])).
% 1.53/0.59  fof(f67,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f32])).
% 1.53/0.59  fof(f32,plain,(
% 1.53/0.59    ! [X0] : (! [X1] : (k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.53/0.59    inference(ennf_transformation,[],[f23])).
% 1.53/0.59  fof(f23,axiom,(
% 1.53/0.59    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).
% 1.53/0.59  fof(f586,plain,(
% 1.53/0.59    k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 1.53/0.59    inference(resolution,[],[f190,f123])).
% 1.53/0.59  fof(f190,plain,(
% 1.53/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,X2) | ~r1_xboole_0(sK1,X2) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = X2) )),
% 1.53/0.59    inference(subsumption_resolution,[],[f187,f106])).
% 1.53/0.59  fof(f187,plain,(
% 1.53/0.59    ( ! [X2] : (~l1_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,X2) | ~r1_xboole_0(sK1,X2) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = X2) )),
% 1.53/0.59    inference(resolution,[],[f71,f63])).
% 1.53/0.59  fof(f71,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2) | ~r1_xboole_0(X1,X2) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2) )),
% 1.53/0.59    inference(cnf_transformation,[],[f36])).
% 1.53/0.59  fof(f36,plain,(
% 1.53/0.59    ! [X0] : (! [X1] : (! [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | ~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.53/0.59    inference(flattening,[],[f35])).
% 1.53/0.59  fof(f35,plain,(
% 1.53/0.59    ! [X0] : (! [X1] : (! [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | (~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.53/0.59    inference(ennf_transformation,[],[f26])).
% 1.53/0.59  fof(f26,axiom,(
% 1.53/0.59    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).
% 1.53/0.59  fof(f174,plain,(
% 1.53/0.59    ~v4_pre_topc(sK1,sK0) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 1.53/0.59    inference(subsumption_resolution,[],[f172,f64])).
% 1.53/0.59  fof(f172,plain,(
% 1.53/0.59    ~l1_pre_topc(sK0) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(resolution,[],[f76,f63])).
% 1.53/0.59  fof(f76,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f40])).
% 1.53/0.59  fof(f40,plain,(
% 1.53/0.59    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.59    inference(ennf_transformation,[],[f18])).
% 1.53/0.59  fof(f18,axiom,(
% 1.53/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).
% 1.53/0.59  fof(f62,plain,(
% 1.53/0.59    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(cnf_transformation,[],[f30])).
% 1.53/0.59  fof(f1626,plain,(
% 1.53/0.59    v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(subsumption_resolution,[],[f1625,f64])).
% 1.53/0.59  fof(f1625,plain,(
% 1.53/0.59    ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(subsumption_resolution,[],[f1624,f63])).
% 1.53/0.59  fof(f1624,plain,(
% 1.53/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(subsumption_resolution,[],[f1623,f1580])).
% 1.53/0.59  fof(f1623,plain,(
% 1.53/0.59    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 1.53/0.59    inference(superposition,[],[f75,f1545])).
% 1.53/0.59  fof(f75,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f40])).
% 1.53/0.59  % SZS output end Proof for theBenchmark
% 1.53/0.59  % (24204)------------------------------
% 1.53/0.59  % (24204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (24204)Termination reason: Refutation
% 1.53/0.59  
% 1.53/0.59  % (24204)Memory used [KB]: 3454
% 1.53/0.59  % (24204)Time elapsed: 0.166 s
% 1.53/0.59  % (24204)------------------------------
% 1.53/0.59  % (24204)------------------------------
% 1.53/0.59  % (24186)Success in time 0.227 s
%------------------------------------------------------------------------------
