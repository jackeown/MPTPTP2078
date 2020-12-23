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
% DateTime   : Thu Dec  3 13:10:05 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   71 (1380 expanded)
%              Number of leaves         :   13 ( 300 expanded)
%              Depth                    :   15
%              Number of atoms          :  238 (6876 expanded)
%              Number of equality atoms :   22 ( 889 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f621,plain,(
    $false ),
    inference(subsumption_resolution,[],[f601,f422])).

fof(f422,plain,(
    ~ r2_orders_2(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f258,f412])).

fof(f412,plain,(
    k1_xboole_0 = sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(unit_resulting_resolution,[],[f341,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f341,plain,(
    v1_xboole_0(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1))) ),
    inference(unit_resulting_resolution,[],[f40,f325,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f325,plain,(
    ! [X0] : m1_subset_1(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f41,f277,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f277,plain,(
    r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f37,f35,f39,f36,f33,f41,f171,f170,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f170,plain,(
    r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(unit_resulting_resolution,[],[f72,f167,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f167,plain,(
    m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f35,f37,f36,f39,f38,f33,f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f72,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f34,f71])).

fof(f71,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f69,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f69,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f39,f43])).

fof(f43,plain,(
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

fof(f34,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

fof(f171,plain,(
    m1_subset_1(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f72,f167,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | m1_subset_1(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f33,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f258,plain,(
    ~ r2_orders_2(sK0,sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1))) ),
    inference(unit_resulting_resolution,[],[f39,f171,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f601,plain,(
    r2_orders_2(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f39,f37,f35,f36,f429,f169,f429,f431,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f431,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f327,f412])).

fof(f327,plain,(
    ! [X0] : r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f41,f277,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f169,plain,(
    m1_subset_1(k3_orders_2(sK0,k3_orders_2(sK0,k1_xboole_0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f35,f37,f36,f39,f38,f33,f167,f63])).

fof(f429,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f325,f412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:03:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (5808)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (5824)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (5806)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (5806)Refutation not found, incomplete strategy% (5806)------------------------------
% 0.22/0.52  % (5806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5823)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (5829)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (5806)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5806)Memory used [KB]: 10618
% 0.22/0.53  % (5806)Time elapsed: 0.092 s
% 0.22/0.53  % (5806)------------------------------
% 0.22/0.53  % (5806)------------------------------
% 0.22/0.53  % (5818)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (5805)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (5827)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (5809)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (5807)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (5811)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (5810)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (5810)Refutation not found, incomplete strategy% (5810)------------------------------
% 0.22/0.54  % (5810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5828)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (5810)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5810)Memory used [KB]: 6140
% 0.22/0.54  % (5810)Time elapsed: 0.072 s
% 0.22/0.54  % (5810)------------------------------
% 0.22/0.54  % (5810)------------------------------
% 0.22/0.54  % (5815)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (5816)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (5819)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (5822)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (5825)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (5817)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (5820)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (5831)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (5812)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (5813)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.56  % (5826)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.56  % (5814)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.56  % (5821)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (5811)Refutation not found, incomplete strategy% (5811)------------------------------
% 0.22/0.57  % (5811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (5811)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (5811)Memory used [KB]: 10618
% 0.22/0.57  % (5811)Time elapsed: 0.147 s
% 0.22/0.57  % (5811)------------------------------
% 0.22/0.57  % (5811)------------------------------
% 1.50/0.57  % (5812)Refutation found. Thanks to Tanya!
% 1.50/0.57  % SZS status Theorem for theBenchmark
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f621,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(subsumption_resolution,[],[f601,f422])).
% 1.50/0.57  fof(f422,plain,(
% 1.50/0.57    ~r2_orders_2(sK0,k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(backward_demodulation,[],[f258,f412])).
% 1.50/0.57  fof(f412,plain,(
% 1.50/0.57    k1_xboole_0 = sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f341,f47])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f22])).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.50/0.57  fof(f341,plain,(
% 1.50/0.57    v1_xboole_0(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f40,f325,f52])).
% 1.50/0.57  fof(f52,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f25])).
% 1.50/0.57  fof(f25,plain,(
% 1.50/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f4])).
% 1.50/0.57  fof(f4,axiom,(
% 1.50/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.50/0.57  fof(f325,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),X0)) )),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f41,f277,f64])).
% 1.50/0.57  fof(f64,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f32])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.50/0.57    inference(flattening,[],[f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.50/0.57    inference(ennf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.50/0.57  fof(f277,plain,(
% 1.50/0.57    r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f38,f37,f35,f39,f36,f33,f41,f171,f170,f49])).
% 1.50/0.57  fof(f49,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f24,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.57    inference(flattening,[],[f23])).
% 1.50/0.57  fof(f23,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f14])).
% 1.50/0.57  fof(f14,axiom,(
% 1.50/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 1.50/0.57  fof(f170,plain,(
% 1.50/0.57    r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f72,f167,f56])).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f27])).
% 1.50/0.57  fof(f27,plain,(
% 1.50/0.57    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.57    inference(flattening,[],[f26])).
% 1.50/0.57  fof(f26,plain,(
% 1.50/0.57    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f6])).
% 1.50/0.57  fof(f6,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 1.50/0.57  fof(f167,plain,(
% 1.50/0.57    m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f35,f37,f36,f39,f38,f33,f41,f63])).
% 1.50/0.57  fof(f63,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.57    inference(flattening,[],[f29])).
% 1.50/0.57  fof(f29,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f12])).
% 1.50/0.57  fof(f12,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 1.50/0.57  fof(f72,plain,(
% 1.50/0.57    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1)),
% 1.50/0.57    inference(backward_demodulation,[],[f34,f71])).
% 1.50/0.57  fof(f71,plain,(
% 1.50/0.57    k1_xboole_0 = k1_struct_0(sK0)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f69,f42])).
% 1.50/0.57  fof(f42,plain,(
% 1.50/0.57    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f19])).
% 1.50/0.57  fof(f19,plain,(
% 1.50/0.57    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,axiom,(
% 1.50/0.57    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 1.50/0.57  fof(f69,plain,(
% 1.50/0.57    l1_struct_0(sK0)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f39,f43])).
% 1.50/0.57  fof(f43,plain,(
% 1.50/0.57    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f20])).
% 1.50/0.57  fof(f20,plain,(
% 1.50/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f13])).
% 1.50/0.57  fof(f13,axiom,(
% 1.50/0.57    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.50/0.57  fof(f34,plain,(
% 1.50/0.57    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f18,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.50/0.57    inference(flattening,[],[f17])).
% 1.50/0.57  fof(f17,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f16])).
% 1.50/0.57  fof(f16,negated_conjecture,(
% 1.50/0.57    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 1.50/0.57    inference(negated_conjecture,[],[f15])).
% 1.50/0.57  fof(f15,conjecture,(
% 1.50/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).
% 1.50/0.57  fof(f171,plain,(
% 1.50/0.57    m1_subset_1(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f72,f167,f55])).
% 1.50/0.57  fof(f55,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1),X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f27])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f36,plain,(
% 1.50/0.57    v3_orders_2(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f39,plain,(
% 1.50/0.57    l1_orders_2(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ~v2_struct_0(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f37,plain,(
% 1.50/0.57    v4_orders_2(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f38,plain,(
% 1.50/0.57    v5_orders_2(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f41,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.50/0.57  fof(f40,plain,(
% 1.50/0.57    v1_xboole_0(k1_xboole_0)),
% 1.50/0.57    inference(cnf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    v1_xboole_0(k1_xboole_0)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.50/0.57  fof(f258,plain,(
% 1.50/0.57    ~r2_orders_2(sK0,sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f39,f171,f68])).
% 1.50/0.57  fof(f68,plain,(
% 1.50/0.57    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 1.50/0.57    inference(duplicate_literal_removal,[],[f65])).
% 1.50/0.57  fof(f65,plain,(
% 1.50/0.57    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 1.50/0.57    inference(equality_resolution,[],[f45])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 != X2 | ~r2_orders_2(X0,X1,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f21])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,axiom,(
% 1.50/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 1.50/0.57  fof(f601,plain,(
% 1.50/0.57    r2_orders_2(sK0,k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f38,f39,f37,f35,f36,f429,f169,f429,f431,f48])).
% 1.50/0.57  fof(f48,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f431,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(k1_xboole_0,X0)) )),
% 1.50/0.57    inference(backward_demodulation,[],[f327,f412])).
% 1.50/0.57  fof(f327,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),X0)) )),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f41,f277,f57])).
% 1.50/0.57  fof(f57,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f28])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f5])).
% 1.50/0.57  fof(f5,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.50/0.57  fof(f169,plain,(
% 1.50/0.57    m1_subset_1(k3_orders_2(sK0,k3_orders_2(sK0,k1_xboole_0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f35,f37,f36,f39,f38,f33,f167,f63])).
% 1.50/0.57  fof(f429,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,X0)) )),
% 1.50/0.57    inference(backward_demodulation,[],[f325,f412])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (5812)------------------------------
% 1.50/0.57  % (5812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (5812)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (5812)Memory used [KB]: 1918
% 1.50/0.57  % (5812)Time elapsed: 0.104 s
% 1.50/0.57  % (5812)------------------------------
% 1.50/0.57  % (5812)------------------------------
% 1.76/0.60  % (5804)Success in time 0.23 s
%------------------------------------------------------------------------------
