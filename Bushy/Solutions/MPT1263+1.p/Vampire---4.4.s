%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t80_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:32 EDT 2019

% Result     : Theorem 75.37s
% Output     : Refutation 75.42s
% Verified   : 
% Statistics : Number of formulae       :  174 (8687 expanded)
%              Number of leaves         :   20 (1947 expanded)
%              Depth                    :   40
%              Number of atoms          :  619 (34159 expanded)
%              Number of equality atoms :   60 (3663 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25506,plain,(
    $false ),
    inference(global_subsumption,[],[f24768,f25505])).

fof(f25505,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f25473,f25474])).

fof(f25474,plain,(
    sK2 = sK4(k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f24782,f24782,f3951])).

fof(f3951,plain,(
    ! [X28,X27] :
      ( sK4(k1_zfmisc_1(X27)) = X28
      | ~ v1_xboole_0(X28)
      | ~ v1_xboole_0(X27) ) ),
    inference(resolution,[],[f212,f704])).

fof(f704,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(k1_zfmisc_1(X0)),X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f268,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',d3_tarski)).

fof(f268,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,sK4(k1_zfmisc_1(X15)))
      | ~ v1_xboole_0(X15) ) ),
    inference(resolution,[],[f101,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',existence_m1_subset_1)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',t5_subset)).

fof(f212,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f92,f171])).

fof(f171,plain,(
    ! [X4,X5] :
      ( r1_tarski(X4,X5)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f94,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',t7_boole)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',d10_xboole_0)).

fof(f24782,plain,(
    v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f24735,f5950])).

fof(f5950,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_xboole_0(sK2) ),
    inference(duplicate_literal_removal,[],[f5946])).

fof(f5946,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_xboole_0(sK2)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f5945,f386])).

fof(f386,plain,
    ( r2_hidden(o_2_1_tops_1(sK0,sK2),sK2)
    | v1_xboole_0(sK2)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f309,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',t2_subset)).

fof(f309,plain,
    ( m1_subset_1(o_2_1_tops_1(sK0,sK2),sK2)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f68,f67,f301])).

fof(f301,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(o_2_1_tops_1(sK0,sK2),sK2)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f87,f61])).

fof(f61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( r1_xboole_0(X1,X2)
                      & v3_pre_topc(X2,X0)
                      & k1_xboole_0 != X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',t80_tops_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(o_2_1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => m1_subset_1(o_2_1_tops_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',dt_o_2_1_tops_1)).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5945,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(global_subsumption,[],[f64,f247,f277,f5944])).

fof(f5944,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | ~ r1_xboole_0(sK1,sK2)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f5918])).

fof(f5918,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | ~ r1_xboole_0(sK1,sK2)
      | ~ v1_tops_1(sK1,sK0)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f2599,f66])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f2599,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK2)
      | ~ r1_xboole_0(X2,sK2)
      | ~ v1_tops_1(X2,sK0)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(global_subsumption,[],[f68,f67,f63,f1078,f2598])).

fof(f2598,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r1_xboole_0(X2,sK2)
      | v2_struct_0(sK0)
      | ~ v1_tops_1(X2,sK0)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f2571,f118])).

fof(f118,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f106,f70])).

fof(f70,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',d3_struct_0)).

fof(f106,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',dt_l1_pre_topc)).

fof(f2571,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,k2_struct_0(sK0))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r1_xboole_0(X2,sK2)
      | v2_struct_0(sK0)
      | ~ v1_tops_1(X2,sK0)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f577,f61])).

fof(f577,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,k2_struct_0(X0))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | v2_struct_0(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f574])).

fof(f574,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k2_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(superposition,[],[f76,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',d3_tops_1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',t39_tops_1)).

fof(f1078,plain,(
    ~ v2_struct_0(sK0) ),
    inference(global_subsumption,[],[f461,f977,f1057])).

fof(f1057,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_struct_0(sK0) ),
    inference(superposition,[],[f62,f1042])).

fof(f1042,plain,
    ( sK1 = sK2
    | ~ v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f1039])).

fof(f1039,plain,
    ( ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0)
    | sK1 = sK2 ),
    inference(resolution,[],[f989,f489])).

fof(f489,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ v2_struct_0(sK0)
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ v2_struct_0(sK0)
      | sK1 = X0
      | ~ v2_struct_0(sK0) ) ),
    inference(superposition,[],[f273,f461])).

fof(f273,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | ~ v2_struct_0(sK0)
      | sK1 = X2 ) ),
    inference(resolution,[],[f270,f92])).

fof(f270,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ v2_struct_0(sK0) ) ),
    inference(resolution,[],[f257,f94])).

fof(f257,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v2_struct_0(sK0) ) ),
    inference(global_subsumption,[],[f106,f255])).

fof(f255,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ l1_struct_0(sK0)
      | ~ v2_struct_0(sK0) ) ),
    inference(resolution,[],[f252,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',fc1_struct_0)).

fof(f252,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f246,f99])).

fof(f246,plain,(
    ! [X9] :
      ( r2_hidden(X9,u1_struct_0(sK0))
      | ~ r2_hidden(X9,sK1) ) ),
    inference(resolution,[],[f93,f121])).

fof(f121,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f66,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',t3_subset)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f989,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | ~ v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f978])).

fof(f978,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK0)
      | ~ v2_struct_0(sK0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f977,f589])).

fof(f589,plain,(
    ! [X0] :
      ( ~ v1_tops_1(sK1,sK0)
      | ~ v2_struct_0(sK0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f588,f94])).

fof(f588,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_tops_1(sK1,sK0)
      | ~ v2_struct_0(sK0) ) ),
    inference(global_subsumption,[],[f106,f586])).

fof(f586,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_tops_1(sK1,sK0)
      | ~ l1_struct_0(sK0)
      | ~ v2_struct_0(sK0) ) ),
    inference(resolution,[],[f262,f81])).

fof(f262,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK2)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f101,f61])).

fof(f62,plain,
    ( k1_xboole_0 != sK2
    | ~ v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f977,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v2_struct_0(sK0) ),
    inference(global_subsumption,[],[f106,f976])).

fof(f976,plain,
    ( ~ v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f974])).

fof(f974,plain,
    ( ~ v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f973,f81])).

fof(f973,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f68,f66,f218,f972])).

fof(f972,plain,
    ( u1_struct_0(sK0) != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f959,f118])).

fof(f959,plain,
    ( k2_struct_0(sK0) != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f73,f462])).

fof(f462,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f273,f347])).

fof(f347,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f336,f218])).

fof(f336,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f321,f97])).

fof(f321,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f68,f66,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',dt_k2_pre_topc)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f218,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f215,f171])).

fof(f215,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f92,f121])).

fof(f461,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f273,f168])).

fof(f168,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f115,f94])).

fof(f115,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f112,f99])).

fof(f112,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f110,f69])).

fof(f69,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',dt_o_0_0_xboole_0)).

fof(f110,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unit_resulting_resolution,[],[f69,f75])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',t6_boole)).

fof(f63,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f277,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK2)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f100,f61])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',t4_subset)).

fof(f247,plain,(
    ! [X10] :
      ( r2_hidden(X10,u1_struct_0(sK0))
      | ~ r2_hidden(X10,sK2)
      | ~ v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f93,f124])).

fof(f124,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f97,f61])).

fof(f64,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f24735,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f106,f346,f611,f1649,f24734])).

fof(f24734,plain,
    ( r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | v1_tops_1(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f24728,f118])).

fof(f24728,plain,
    ( v1_tops_1(sK1,sK0)
    | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ l1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f24693])).

fof(f24693,plain,
    ( v1_tops_1(sK1,sK0)
    | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f19125,f1079])).

fof(f1079,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(k2_struct_0(X0),X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | r1_tarski(k2_struct_0(X0),X1) ) ),
    inference(resolution,[],[f278,f94])).

fof(f278,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_struct_0(X3))
      | m1_subset_1(X2,u1_struct_0(X3))
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',dt_k2_struct_0)).

fof(f19125,plain,(
    ! [X26] :
      ( ~ m1_subset_1(sK5(X26,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
      | v1_tops_1(sK1,sK0)
      | r1_tarski(X26,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f19098,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f19098,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v1_tops_1(sK1,sK0) ) ),
    inference(global_subsumption,[],[f68,f67,f66,f115,f1078,f19092])).

fof(f19092,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_xboole_0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | v1_tops_1(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f19055])).

fof(f19055,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_xboole_0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v1_tops_1(sK1,sK0) ) ),
    inference(superposition,[],[f79,f5354])).

fof(f5354,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(sK0,sK1,X0)
      | r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_tops_1(sK1,sK0) ) ),
    inference(global_subsumption,[],[f68,f67,f66,f1078,f5353])).

fof(f5353,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | k1_xboole_0 = sK3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_tops_1(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f5350])).

fof(f5350,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | k1_xboole_0 = sK3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_tops_1(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f1915,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1915,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK3(sK0,sK1,X0),sK0)
      | r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | k1_xboole_0 = sK3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_tops_1(sK1,sK0) ) ),
    inference(global_subsumption,[],[f68,f67,f66,f1078,f1914])).

fof(f1914,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | k1_xboole_0 = sK3(sK0,sK1,X0)
      | ~ v3_pre_topc(sK3(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1911])).

fof(f1911,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | k1_xboole_0 = sK3(sK0,sK1,X0)
      | ~ v3_pre_topc(sK3(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f551,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,sK3(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f551,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK1,sK3(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X1,k2_pre_topc(sK0,X0))
      | k1_xboole_0 = sK3(sK0,X0,X1)
      | ~ v3_pre_topc(sK3(sK0,X0,X1),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(global_subsumption,[],[f68,f67,f543])).

fof(f543,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X1,k2_pre_topc(sK0,X0))
      | k1_xboole_0 = sK3(sK0,X0,X1)
      | ~ v3_pre_topc(sK3(sK0,X0,X1),sK0)
      | ~ r1_xboole_0(sK1,sK3(sK0,X0,X1))
      | v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f77,f65])).

fof(f65,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,sK0)
      | ~ r1_xboole_0(sK1,X2)
      | v1_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK3(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1649,plain,
    ( ~ v1_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f68,f66,f1648])).

fof(f1648,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f1647])).

fof(f1647,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f1639,f118])).

fof(f1639,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(superposition,[],[f73,f607])).

fof(f607,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(global_subsumption,[],[f68,f321,f606])).

fof(f606,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f599,f118])).

fof(f599,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(superposition,[],[f405,f74])).

fof(f405,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f68,f66,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tops_1__t80_tops_1.p',projectivity_k2_pre_topc)).

fof(f611,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(global_subsumption,[],[f68,f321,f610])).

fof(f610,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f604,f118])).

fof(f604,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(superposition,[],[f73,f405])).

fof(f346,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f336,f92])).

fof(f25473,plain,(
    k1_xboole_0 = sK4(k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f112,f24782,f3951])).

fof(f24768,plain,(
    k1_xboole_0 != sK2 ),
    inference(unit_resulting_resolution,[],[f24735,f62])).
%------------------------------------------------------------------------------
