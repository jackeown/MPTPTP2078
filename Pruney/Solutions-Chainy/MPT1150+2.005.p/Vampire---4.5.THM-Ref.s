%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 310 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   22
%              Number of atoms          :  345 (1372 expanded)
%              Number of equality atoms :   38 ( 213 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(resolution,[],[f525,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f525,plain,(
    ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(resolution,[],[f524,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f524,plain,(
    ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(global_subsumption,[],[f38,f523])).

fof(f523,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f516])).

fof(f516,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f250,f455])).

fof(f455,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_orders_2(sK0,X0)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = k1_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f438,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f438,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f436])).

fof(f436,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(superposition,[],[f426,f193])).

fof(f193,plain,(
    ! [X0] :
      ( k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f80,f154])).

fof(f154,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f136,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f136,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f37,plain,(
    l1_orders_2(sK0) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(global_subsumption,[],[f37,f36,f35,f34,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f426,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(superposition,[],[f192,f249])).

fof(f249,plain,(
    ! [X8,X7] :
      ( sK2(X8,sK0,X7) = X8
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(forward_demodulation,[],[f84,f154])).

fof(f84,plain,(
    ! [X8,X7] :
      ( sK2(X8,sK0,X7) = X8
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(global_subsumption,[],[f37,f36,f35,f34,f76])).

fof(f76,plain,(
    ! [X8,X7] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X8,sK0,X7) = X8
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(resolution,[],[f33,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK2(X0,X1,X2) = X0
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,sK0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(global_subsumption,[],[f33,f34,f35,f36,f37,f177,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(sK2(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(sK2(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(forward_demodulation,[],[f189,f154])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2(X0,sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(sK2(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(forward_demodulation,[],[f188,f154])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2(X0,sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(sK2(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(resolution,[],[f187,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,X4,sK2(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f187,plain,(
    ! [X15] :
      ( ~ r2_orders_2(sK0,X15,X15)
      | ~ m1_subset_1(X15,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f145,f154])).

fof(f145,plain,(
    ! [X15] :
      ( ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X15,X15) ) ),
    inference(resolution,[],[f37,f71])).

fof(f71,plain,(
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
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f177,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK2(X11,sK0,X12),k2_struct_0(sK0))
      | ~ r2_hidden(X11,a_2_0_orders_2(sK0,X12)) ) ),
    inference(global_subsumption,[],[f176])).

fof(f176,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X10,a_2_0_orders_2(sK0,X9))
      | m1_subset_1(sK2(X10,sK0,X9),k2_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f33,f34,f35,f36,f37,f160])).

fof(f160,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | m1_subset_1(sK2(X10,sK0,X9),k2_struct_0(sK0))
      | ~ r2_hidden(X10,a_2_0_orders_2(sK0,X9)) ) ),
    inference(superposition,[],[f62,f154])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f250,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_orders_2(sK0,X0)),k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = k1_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f240,f49])).

fof(f240,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_orders_2(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X4,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f195,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f195,plain,(
    ! [X1] :
      ( m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f194,f154])).

fof(f194,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f81,f154])).

fof(f81,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f37,f36,f35,f34,f73])).

fof(f73,plain,(
    ! [X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f33,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f38,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:05:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (10423)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (10431)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (10414)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (10410)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (10434)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (10415)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (10429)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (10422)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (10417)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (10433)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (10420)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (10421)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (10411)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (10412)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (10430)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (10419)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (10427)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (10426)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (10413)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (10424)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (10435)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (10428)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (10432)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (10418)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (10416)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (10425)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (10416)Refutation not found, incomplete strategy% (10416)------------------------------
% 0.21/0.55  % (10416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10416)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10416)Memory used [KB]: 10618
% 0.21/0.55  % (10416)Time elapsed: 0.104 s
% 0.21/0.55  % (10416)------------------------------
% 0.21/0.55  % (10416)------------------------------
% 0.21/0.55  % (10430)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f528,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(resolution,[],[f525,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f525,plain,(
% 0.21/0.55    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.21/0.55    inference(resolution,[],[f524,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f524,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.55    inference(global_subsumption,[],[f38,f523])).
% 0.21/0.55  fof(f523,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f516])).
% 0.21/0.55  fof(f516,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.55    inference(resolution,[],[f250,f455])).
% 0.21/0.55  fof(f455,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK1(k1_orders_2(sK0,X0)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k1_orders_2(sK0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f438,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.55  fof(f438,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k1_orders_2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f436])).
% 0.21/0.55  fof(f436,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k1_orders_2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.55    inference(superposition,[],[f426,f193])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    ( ! [X0] : (k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f80,f154])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.55    inference(resolution,[],[f136,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    l1_struct_0(sK0)),
% 0.21/0.55    inference(resolution,[],[f37,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    l1_orders_2(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f15])).
% 0.21/0.55  fof(f15,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.21/0.55    inference(global_subsumption,[],[f37,f36,f35,f34,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f33,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ~v2_struct_0(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    v3_orders_2(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    v4_orders_2(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    v5_orders_2(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f426,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f423])).
% 0.21/0.55  fof(f423,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 0.21/0.55    inference(superposition,[],[f192,f249])).
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    ( ! [X8,X7] : (sK2(X8,sK0,X7) = X8 | ~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f84,f154])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X8,X7] : (sK2(X8,sK0,X7) = X8 | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.21/0.55    inference(global_subsumption,[],[f37,f36,f35,f34,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X8,X7] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X8,sK0,X7) = X8 | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.21/0.55    inference(resolution,[],[f33,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(X0,sK0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 0.21/0.55    inference(global_subsumption,[],[f33,f34,f35,f36,f37,f177,f191])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~r2_hidden(sK2(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~r2_hidden(sK2(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f189,f154])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2(X0,sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(sK2(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f188,f154])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2(X0,sK0,X1),k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(X0,sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(sK2(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 0.21/0.55    inference(resolution,[],[f187,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (v2_struct_0(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(X4,X2) | r2_orders_2(X1,X4,sK2(X0,X1,X2)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    ( ! [X15] : (~r2_orders_2(sK0,X15,X15) | ~m1_subset_1(X15,k2_struct_0(sK0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f145,f154])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    ( ! [X15] : (~m1_subset_1(X15,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X15,X15)) )),
% 0.21/0.55    inference(resolution,[],[f37,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.55    inference(equality_resolution,[],[f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 != X2 | ~r2_orders_2(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    ( ! [X12,X11] : (~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK2(X11,sK0,X12),k2_struct_0(sK0)) | ~r2_hidden(X11,a_2_0_orders_2(sK0,X12))) )),
% 0.21/0.55    inference(global_subsumption,[],[f176])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X10,a_2_0_orders_2(sK0,X9)) | m1_subset_1(sK2(X10,sK0,X9),k2_struct_0(sK0))) )),
% 0.21/0.55    inference(global_subsumption,[],[f33,f34,f35,f36,f37,f160])).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | m1_subset_1(sK2(X10,sK0,X9),k2_struct_0(sK0)) | ~r2_hidden(X10,a_2_0_orders_2(sK0,X9))) )),
% 0.21/0.55    inference(superposition,[],[f62,f154])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f250,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK1(k1_orders_2(sK0,X0)),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k1_orders_2(sK0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f240,f49])).
% 0.21/0.55  fof(f240,plain,(
% 0.21/0.55    ( ! [X4,X3] : (~r2_hidden(X4,k1_orders_2(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X4,k2_struct_0(sK0))) )),
% 0.21/0.55    inference(resolution,[],[f195,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    ( ! [X1] : (m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f194,f154])).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f81,f154])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(global_subsumption,[],[f37,f36,f35,f34,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(resolution,[],[f33,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (10430)------------------------------
% 0.21/0.55  % (10430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10430)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (10430)Memory used [KB]: 11257
% 0.21/0.55  % (10430)Time elapsed: 0.130 s
% 0.21/0.55  % (10430)------------------------------
% 0.21/0.55  % (10430)------------------------------
% 0.21/0.56  % (10409)Success in time 0.197 s
%------------------------------------------------------------------------------
