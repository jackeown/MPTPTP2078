%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1152+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:22 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 220 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   32
%              Number of atoms          :  336 ( 932 expanded)
%              Number of equality atoms :   28 ( 119 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(resolution,[],[f354,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f354,plain,(
    ! [X3] : ~ m1_subset_1(X3,k2_orders_2(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f353,f107])).

fof(f107,plain,(
    k1_xboole_0 != k2_orders_2(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f43,f103])).

fof(f103,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f75,f46])).

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

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
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
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f43,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f353,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k2_orders_2(sK0,u1_struct_0(sK0)))
      | k1_xboole_0 = k2_orders_2(sK0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f349,f48])).

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

fof(f349,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_orders_2(sK0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k2_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f348,f52])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f348,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_orders_2(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f346,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
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

fof(f346,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,u1_struct_0(sK0)))
      | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f342,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f342,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f335,f85])).

fof(f85,plain,(
    ! [X0] :
      ( k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f84,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f83,f41])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f82,f40])).

fof(f40,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f76,f39])).

fof(f39,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f335,plain,(
    ! [X0] : ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f333,f70])).

fof(f333,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f332,f58])).

fof(f332,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f331,f38])).

fof(f331,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f330,f42])).

fof(f330,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f329,f41])).

fof(f329,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f328,f40])).

fof(f328,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f327,f39])).

fof(f327,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f318,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f318,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3(X1,sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f316,f106])).

fof(f106,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f105,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f75])).

fof(f104,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f50,f103])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f316,plain,(
    ! [X1] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(X1,sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f245,f70])).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(sK0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK3(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) ) ),
    inference(resolution,[],[f119,f58])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3(X1,sK0,X0),X0) ) ),
    inference(resolution,[],[f118,f52])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,sK0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f115,f67])).

fof(f67,plain,(
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

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,sK0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f90,f81])).

fof(f81,plain,(
    ! [X10] :
      ( ~ r2_orders_2(sK0,X10,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f42,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_orders_2(X1,X0,X0) ) ),
    inference(condensation,[],[f66])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(f90,plain,(
    ! [X2,X3,X1] :
      ( r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f89,f67])).

fof(f89,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f88,f38])).

fof(f88,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,(
    ! [X2,X3,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f77,plain,(
    ! [X2,X3,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1)) ) ),
    inference(resolution,[],[f42,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,sK3(X0,X1,X2),X4)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
