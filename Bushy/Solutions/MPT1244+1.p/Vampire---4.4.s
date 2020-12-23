%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t58_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:30 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 361 expanded)
%              Number of leaves         :   12 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 (1132 expanded)
%              Number of equality atoms :   25 ( 289 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1422,plain,(
    $false ),
    inference(global_subsumption,[],[f1219,f1420])).

fof(f1420,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f63,f617,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',d10_xboole_0)).

fof(f617,plain,(
    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) ),
    inference(unit_resulting_resolution,[],[f61,f106,f344,f360,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',t49_pre_topc)).

fof(f360,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f357,f126])).

fof(f126,plain,(
    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f61,f62,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',projectivity_k1_tops_1)).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_pre_topc(sK0,k1_tops_1(sK0,X1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X1))))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X0,k1_tops_1(X0,sK1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,sK1))))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',t58_tops_1)).

fof(f357,plain,(
    r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f61,f106,f142,f146,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',t48_tops_1)).

fof(f146,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f61,f106,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',t48_pre_topc)).

fof(f142,plain,(
    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f61,f106,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',dt_k2_pre_topc)).

fof(f344,plain,(
    m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f61,f142,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',dt_k1_tops_1)).

fof(f106,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f61,f62,f69])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f63,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f1219,plain,(
    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f344,f347,f461])).

fof(f461,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f460,f61])).

fof(f460,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f457,f142])).

fof(f457,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f66,f141])).

fof(f141,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f61,f106,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',projectivity_k2_pre_topc)).

fof(f347,plain,(
    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f61,f142,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t58_tops_1.p',t44_tops_1)).
%------------------------------------------------------------------------------
