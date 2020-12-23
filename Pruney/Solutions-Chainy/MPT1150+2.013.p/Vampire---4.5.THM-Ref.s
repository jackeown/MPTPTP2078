%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:45 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 338 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  348 (1422 expanded)
%              Number of equality atoms :   26 ( 208 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f676,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f84,f67,f673])).

fof(f673,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f34,f167,f672])).

fof(f672,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(forward_demodulation,[],[f671,f70])).

fof(f70,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f68,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f38,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f671,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f670])).

fof(f670,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(forward_demodulation,[],[f669,f70])).

fof(f669,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(forward_demodulation,[],[f668,f143])).

fof(f143,plain,(
    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f142,f70])).

fof(f142,plain,(
    k1_orders_2(sK0,u1_struct_0(sK0)) = a_2_0_orders_2(sK0,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f38,f37,f36,f67,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f668,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(forward_demodulation,[],[f667,f70])).

fof(f667,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(forward_demodulation,[],[f666,f70])).

fof(f666,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f663])).

fof(f663,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f474,f181])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X2,X0,X1),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f474,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK2(X3,sK0,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4)) ) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f34,f186,f469])).

fof(f469,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK2(X3,sK0,X4),k2_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2(X3,sK0,X4),X4)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4)) ) ),
    inference(superposition,[],[f252,f70])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(X2,X0,X1),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(sK2(X2,X0,X1),X1)
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK2(X2,X0,X1),u1_struct_0(X0))
      | ~ r2_hidden(sK2(X2,X0,X1),X1)
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X1))
      | ~ m1_subset_1(sK2(X2,X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | X1 != X2
      | ~ r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_orders_2(X1,X4,sK2(X0,X1,X2))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f186,plain,(
    ! [X4,X3] :
      ( m1_subset_1(sK2(X3,sK0,X4),k2_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4)) ) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f34,f184])).

fof(f184,plain,(
    ! [X4,X3] :
      ( m1_subset_1(sK2(X3,sK0,X4),k2_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4)) ) ),
    inference(superposition,[],[f58,f70])).

fof(f167,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f84,f154,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f154,plain,(
    m1_subset_1(k1_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f147,f70])).

fof(f147,plain,(
    m1_subset_1(k1_orders_2(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f34,f35,f38,f37,f36,f67,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f43,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f84,plain,(
    r2_hidden(sK1(k1_xboole_0,k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f39,f74,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f74,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f40,f67,f61])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (23127)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (23109)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (23119)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (23131)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (23123)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (23113)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (23112)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (23126)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (23115)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (23131)Refutation not found, incomplete strategy% (23131)------------------------------
% 0.21/0.53  % (23131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23131)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23131)Memory used [KB]: 10746
% 0.21/0.53  % (23131)Time elapsed: 0.065 s
% 0.21/0.53  % (23131)------------------------------
% 0.21/0.53  % (23131)------------------------------
% 0.21/0.53  % (23118)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (23138)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (23116)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (23111)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (23134)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (23130)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (23139)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (23122)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (23129)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (23136)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (23106)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (23128)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (23133)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (23121)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (23120)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (23135)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (23124)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (23125)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.56  % (23117)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.55/0.56  % (23107)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.55/0.57  % (23132)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.05/0.63  % (23133)Refutation found. Thanks to Tanya!
% 2.05/0.63  % SZS status Theorem for theBenchmark
% 2.05/0.63  % SZS output start Proof for theBenchmark
% 2.05/0.63  fof(f676,plain,(
% 2.05/0.63    $false),
% 2.05/0.63    inference(unit_resulting_resolution,[],[f84,f67,f673])).
% 2.05/0.63  fof(f673,plain,(
% 2.05/0.63    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))) )),
% 2.05/0.63    inference(global_subsumption,[],[f38,f37,f36,f35,f34,f167,f672])).
% 2.05/0.63  fof(f672,plain,(
% 2.05/0.63    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v3_orders_2(sK0)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f671,f70])).
% 2.05/0.63  fof(f70,plain,(
% 2.05/0.63    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 2.05/0.63    inference(unit_resulting_resolution,[],[f68,f44])).
% 2.05/0.63  fof(f44,plain,(
% 2.05/0.63    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f19])).
% 2.05/0.63  fof(f19,plain,(
% 2.05/0.63    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f9])).
% 2.05/0.63  fof(f9,axiom,(
% 2.05/0.63    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.05/0.63  fof(f68,plain,(
% 2.05/0.63    l1_struct_0(sK0)),
% 2.05/0.63    inference(unit_resulting_resolution,[],[f38,f45])).
% 2.05/0.63  fof(f45,plain,(
% 2.05/0.63    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f20])).
% 2.05/0.63  fof(f20,plain,(
% 2.05/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f13])).
% 2.05/0.63  fof(f13,axiom,(
% 2.05/0.63    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 2.05/0.63  fof(f671,plain,(
% 2.05/0.63    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v3_orders_2(sK0)) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f670])).
% 2.05/0.63  fof(f670,plain,(
% 2.05/0.63    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v3_orders_2(sK0)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f669,f70])).
% 2.05/0.63  fof(f669,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v3_orders_2(sK0)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f668,f143])).
% 2.05/0.63  fof(f143,plain,(
% 2.05/0.63    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0))),
% 2.05/0.63    inference(forward_demodulation,[],[f142,f70])).
% 2.05/0.63  fof(f142,plain,(
% 2.05/0.63    k1_orders_2(sK0,u1_struct_0(sK0)) = a_2_0_orders_2(sK0,u1_struct_0(sK0))),
% 2.05/0.63    inference(unit_resulting_resolution,[],[f34,f35,f38,f37,f36,f67,f49])).
% 2.05/0.63  fof(f49,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f23])).
% 2.05/0.63  fof(f23,plain,(
% 2.05/0.63    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.05/0.63    inference(flattening,[],[f22])).
% 2.05/0.63  fof(f22,plain,(
% 2.05/0.63    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f11])).
% 2.05/0.63  fof(f11,axiom,(
% 2.05/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 2.05/0.63  fof(f668,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v3_orders_2(sK0)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f667,f70])).
% 2.05/0.63  fof(f667,plain,(
% 2.05/0.63    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v3_orders_2(sK0)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f666,f70])).
% 2.05/0.63  fof(f666,plain,(
% 2.05/0.63    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v3_orders_2(sK0)) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f663])).
% 2.05/0.63  fof(f663,plain,(
% 2.05/0.63    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | ~v3_orders_2(sK0)) )),
% 2.05/0.63    inference(resolution,[],[f474,f181])).
% 2.05/0.63  fof(f181,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK2(X2,X0,X1),u1_struct_0(X0)) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(X2,a_2_0_orders_2(X0,X1)) | v1_xboole_0(u1_struct_0(X0)) | ~v3_orders_2(X0)) )),
% 2.05/0.63    inference(resolution,[],[f58,f50])).
% 2.05/0.63  fof(f50,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f25])).
% 2.05/0.63  fof(f25,plain,(
% 2.05/0.63    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.05/0.63    inference(flattening,[],[f24])).
% 2.05/0.63  fof(f24,plain,(
% 2.05/0.63    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f6])).
% 2.05/0.63  fof(f6,axiom,(
% 2.05/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.05/0.63  fof(f58,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f30])).
% 2.05/0.63  fof(f30,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.05/0.63    inference(flattening,[],[f29])).
% 2.05/0.63  fof(f29,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.05/0.63    inference(ennf_transformation,[],[f14])).
% 2.05/0.63  fof(f14,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 2.05/0.63  fof(f474,plain,(
% 2.05/0.63    ( ! [X4,X3] : (~r2_hidden(sK2(X3,sK0,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X3,a_2_0_orders_2(sK0,X4))) )),
% 2.05/0.63    inference(global_subsumption,[],[f38,f37,f36,f35,f34,f186,f469])).
% 2.05/0.63  fof(f469,plain,(
% 2.05/0.63    ( ! [X4,X3] : (~m1_subset_1(sK2(X3,sK0,X4),k2_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | ~r2_hidden(sK2(X3,sK0,X4),X4) | v2_struct_0(sK0) | ~r2_hidden(X3,a_2_0_orders_2(sK0,X4))) )),
% 2.05/0.63    inference(superposition,[],[f252,f70])).
% 2.05/0.63  fof(f252,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(X2,X0,X1),u1_struct_0(X0)) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~r2_hidden(sK2(X2,X0,X1),X1) | v2_struct_0(X0) | ~r2_hidden(X2,a_2_0_orders_2(X0,X1))) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f245])).
% 2.05/0.63  fof(f245,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK2(X2,X0,X1),u1_struct_0(X0)) | ~r2_hidden(sK2(X2,X0,X1),X1) | v2_struct_0(X0) | ~r2_hidden(X2,a_2_0_orders_2(X0,X1)) | ~m1_subset_1(sK2(X2,X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.05/0.63    inference(resolution,[],[f57,f66])).
% 2.05/0.63  fof(f66,plain,(
% 2.05/0.63    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f62])).
% 2.05/0.63  fof(f62,plain,(
% 2.05/0.63    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 2.05/0.63    inference(equality_resolution,[],[f47])).
% 2.05/0.63  fof(f47,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 != X2 | ~r2_orders_2(X0,X1,X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f21])).
% 2.05/0.63  fof(f21,plain,(
% 2.05/0.63    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f10])).
% 2.05/0.63  fof(f10,axiom,(
% 2.05/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 2.05/0.63  fof(f57,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X1] : (r2_orders_2(X1,X4,sK2(X0,X1,X2)) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(X4,X2) | v2_struct_0(X1) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f30])).
% 2.05/0.63  fof(f186,plain,(
% 2.05/0.63    ( ! [X4,X3] : (m1_subset_1(sK2(X3,sK0,X4),k2_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X3,a_2_0_orders_2(sK0,X4))) )),
% 2.05/0.63    inference(global_subsumption,[],[f38,f37,f36,f35,f34,f184])).
% 2.05/0.63  fof(f184,plain,(
% 2.05/0.63    ( ! [X4,X3] : (m1_subset_1(sK2(X3,sK0,X4),k2_struct_0(sK0)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(X3,a_2_0_orders_2(sK0,X4))) )),
% 2.05/0.63    inference(superposition,[],[f58,f70])).
% 2.05/0.63  fof(f167,plain,(
% 2.05/0.63    ~v1_xboole_0(k2_struct_0(sK0))),
% 2.05/0.63    inference(unit_resulting_resolution,[],[f84,f154,f61])).
% 2.05/0.63  fof(f61,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f33])).
% 2.05/0.63  fof(f33,plain,(
% 2.05/0.63    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f8])).
% 2.05/0.63  fof(f8,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 2.05/0.63  fof(f154,plain,(
% 2.05/0.63    m1_subset_1(k1_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.05/0.63    inference(forward_demodulation,[],[f147,f70])).
% 2.05/0.63  fof(f147,plain,(
% 2.05/0.63    m1_subset_1(k1_orders_2(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.63    inference(unit_resulting_resolution,[],[f34,f35,f38,f37,f36,f67,f51])).
% 2.05/0.63  fof(f51,plain,(
% 2.05/0.63    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f27])).
% 2.05/0.63  fof(f27,plain,(
% 2.05/0.63    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.05/0.63    inference(flattening,[],[f26])).
% 2.05/0.63  fof(f26,plain,(
% 2.05/0.63    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f12])).
% 2.05/0.63  fof(f12,axiom,(
% 2.05/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 2.05/0.63  fof(f34,plain,(
% 2.05/0.63    ~v2_struct_0(sK0)),
% 2.05/0.63    inference(cnf_transformation,[],[f18])).
% 2.05/0.63  fof(f18,plain,(
% 2.05/0.63    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.05/0.63    inference(flattening,[],[f17])).
% 2.05/0.63  fof(f17,plain,(
% 2.05/0.63    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f16])).
% 2.05/0.63  fof(f16,negated_conjecture,(
% 2.05/0.63    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.05/0.63    inference(negated_conjecture,[],[f15])).
% 2.05/0.63  fof(f15,conjecture,(
% 2.05/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).
% 2.05/0.63  fof(f35,plain,(
% 2.05/0.63    v3_orders_2(sK0)),
% 2.05/0.63    inference(cnf_transformation,[],[f18])).
% 2.05/0.63  fof(f36,plain,(
% 2.05/0.63    v4_orders_2(sK0)),
% 2.05/0.63    inference(cnf_transformation,[],[f18])).
% 2.05/0.63  fof(f37,plain,(
% 2.05/0.63    v5_orders_2(sK0)),
% 2.05/0.63    inference(cnf_transformation,[],[f18])).
% 2.05/0.63  fof(f38,plain,(
% 2.05/0.63    l1_orders_2(sK0)),
% 2.05/0.63    inference(cnf_transformation,[],[f18])).
% 2.05/0.63  fof(f67,plain,(
% 2.05/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.05/0.63    inference(forward_demodulation,[],[f43,f41])).
% 2.05/0.63  fof(f41,plain,(
% 2.05/0.63    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f3])).
% 2.05/0.63  fof(f3,axiom,(
% 2.05/0.63    ! [X0] : k2_subset_1(X0) = X0),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.05/0.63  fof(f43,plain,(
% 2.05/0.63    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f4])).
% 2.05/0.63  fof(f4,axiom,(
% 2.05/0.63    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.05/0.63  fof(f84,plain,(
% 2.05/0.63    r2_hidden(sK1(k1_xboole_0,k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0)))),
% 2.05/0.63    inference(unit_resulting_resolution,[],[f39,f74,f52])).
% 2.05/0.63  fof(f52,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X0 = X1) )),
% 2.05/0.63    inference(cnf_transformation,[],[f28])).
% 2.05/0.63  fof(f28,plain,(
% 2.05/0.63    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.05/0.63    inference(ennf_transformation,[],[f2])).
% 2.05/0.63  fof(f2,axiom,(
% 2.05/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 2.05/0.63  fof(f74,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.05/0.63    inference(unit_resulting_resolution,[],[f40,f67,f61])).
% 2.05/0.63  fof(f40,plain,(
% 2.05/0.63    v1_xboole_0(k1_xboole_0)),
% 2.05/0.63    inference(cnf_transformation,[],[f1])).
% 2.05/0.63  fof(f1,axiom,(
% 2.05/0.63    v1_xboole_0(k1_xboole_0)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.05/0.63  fof(f39,plain,(
% 2.05/0.63    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))),
% 2.05/0.63    inference(cnf_transformation,[],[f18])).
% 2.05/0.63  % SZS output end Proof for theBenchmark
% 2.05/0.63  % (23133)------------------------------
% 2.05/0.63  % (23133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (23133)Termination reason: Refutation
% 2.05/0.63  
% 2.05/0.63  % (23133)Memory used [KB]: 7164
% 2.05/0.63  % (23133)Time elapsed: 0.222 s
% 2.05/0.63  % (23133)------------------------------
% 2.05/0.63  % (23133)------------------------------
% 2.05/0.63  % (23098)Success in time 0.263 s
%------------------------------------------------------------------------------
