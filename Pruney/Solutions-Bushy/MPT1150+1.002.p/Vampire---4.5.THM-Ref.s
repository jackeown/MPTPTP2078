%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1150+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 220 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   32
%              Number of atoms          :  333 ( 929 expanded)
%              Number of equality atoms :   28 ( 119 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(resolution,[],[f217,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f217,plain,(
    ! [X3] : ~ m1_subset_1(X3,k1_orders_2(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f216,f108])).

fof(f108,plain,(
    k1_xboole_0 != k1_orders_2(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f43,f104])).

fof(f104,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f76,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f42,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(f43,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f216,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_orders_2(sK0,u1_struct_0(sK0)))
      | k1_xboole_0 = k1_orders_2(sK0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f199,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f199,plain,(
    ! [X2] :
      ( v1_xboole_0(k1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f197,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f197,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_orders_2(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f195,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f195,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f171,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f166,f86])).

fof(f86,plain,(
    ! [X0] :
      ( k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f84,f41])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f40,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f39,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f166,plain,(
    ! [X0] : ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f164,f71])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f162,f59])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f161,f38])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f42])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f41])).

fof(f159,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f40])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f39])).

fof(f157,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f148,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f148,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK3(X2,sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f145,f107])).

fof(f107,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f106,f38])).

fof(f106,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f76])).

fof(f105,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f50,f104])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f145,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,a_2_0_orders_2(sK0,u1_struct_0(sK0)))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(X2,sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f124,f52])).

fof(f124,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f120,f71])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ r2_hidden(sK3(X0,sK0,X1),X1) ) ),
    inference(resolution,[],[f119,f59])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK3(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f116,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,sK0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f91,f82])).

fof(f82,plain,(
    ! [X10] :
      ( ~ r2_orders_2(sK0,X10,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f42,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_orders_2(X1,X0,X0) ) ),
    inference(condensation,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(f91,plain,(
    ! [X2,X3,X1] :
      ( r2_orders_2(sK0,X2,sK3(X3,sK0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f90,f68])).

fof(f90,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,X2,sK3(X3,sK0,X1))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f89,f38])).

fof(f89,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,X2,sK3(X3,sK0,X1))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f88,f41])).

fof(f88,plain,(
    ! [X2,X3,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,X2,sK3(X3,sK0,X1))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,X2,sK3(X3,sK0,X1))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f78,f39])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,X2,sK3(X3,sK0,X1))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X1)) ) ),
    inference(resolution,[],[f42,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,X4,sK3(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
