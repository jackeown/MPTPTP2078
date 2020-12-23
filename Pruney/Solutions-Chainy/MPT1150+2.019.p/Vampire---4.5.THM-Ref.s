%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 (1052 expanded)
%              Number of leaves         :   11 ( 214 expanded)
%              Depth                    :   29
%              Number of atoms          :  396 (4369 expanded)
%              Number of equality atoms :   48 ( 773 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137,f110])).

fof(f110,plain,(
    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f109,f103])).

fof(f103,plain,(
    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f102,f32])).

fof(f32,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(f102,plain,
    ( sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f101,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK2(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f100,f97])).

fof(f97,plain,(
    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f96,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f96,plain,(
    k1_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))) = a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f95,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f95,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11) ) ),
    inference(subsumption_resolution,[],[f94,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11) ) ),
    inference(subsumption_resolution,[],[f93,f31])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11) ) ),
    inference(subsumption_resolution,[],[f92,f30])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11) ) ),
    inference(subsumption_resolution,[],[f91,f29])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11) ) ),
    inference(subsumption_resolution,[],[f65,f28])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11) ) ),
    inference(superposition,[],[f33,f57])).

fof(f57,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0)))
      | sK2(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f99,f49])).

fof(f99,plain,(
    ! [X0] :
      ( sK2(X0,sK0,k2_struct_0(sK0)) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f98,f49])).

fof(f98,plain,(
    ! [X0] :
      ( sK2(X0,sK0,k2_subset_1(k2_struct_0(sK0))) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0)))) ) ),
    inference(resolution,[],[f90,f44])).

fof(f90,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK2(X10,sK0,X9) = X10
      | ~ r2_hidden(X10,a_2_0_orders_2(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f89,f27])).

fof(f89,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | sK2(X10,sK0,X9) = X10
      | ~ r2_hidden(X10,a_2_0_orders_2(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f88,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | sK2(X10,sK0,X9) = X10
      | ~ r2_hidden(X10,a_2_0_orders_2(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f87,f30])).

fof(f87,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | sK2(X10,sK0,X9) = X10
      | ~ r2_hidden(X10,a_2_0_orders_2(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f86,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | sK2(X10,sK0,X9) = X10
      | ~ r2_hidden(X10,a_2_0_orders_2(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f64,f28])).

fof(f64,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | sK2(X10,sK0,X9) = X10
      | ~ r2_hidden(X10,a_2_0_orders_2(sK0,X9)) ) ),
    inference(superposition,[],[f42,f57])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f109,plain,(
    m1_subset_1(sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f108,f32])).

fof(f108,plain,
    ( m1_subset_1(sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f107,f35])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f106,f97])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0)))
      | m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f105,f49])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f104,f49])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0,sK0,k2_subset_1(k2_struct_0(sK0))),k2_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0)))) ) ),
    inference(resolution,[],[f85,f44])).

fof(f85,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f84,f27])).

fof(f84,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f83,f31])).

fof(f83,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f82,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f81,f29])).

fof(f81,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f63,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(superposition,[],[f41,f57])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f137,plain,(
    ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f136,f57])).

fof(f136,plain,(
    ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f133,f31])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f132,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
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
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f132,plain,(
    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f131,f103])).

fof(f131,plain,(
    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f130,f32])).

fof(f130,plain,
    ( r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f129,f35])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK2(X0,sK0,k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f128,f116])).

fof(f116,plain,(
    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f115,f59])).

fof(f59,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f58,f57])).

fof(f58,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f56,f27])).

fof(f56,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f115,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(resolution,[],[f110,f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f128,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK2(X0,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
      | ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f125,f110])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f124,f97])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f123,f49])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f122,f49])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_subset_1(k2_struct_0(sK0))))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f121,f49])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,k2_subset_1(k2_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_subset_1(k2_struct_0(sK0))))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0)))) ) ),
    inference(resolution,[],[f80,f44])).

fof(f80,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X5,k2_struct_0(sK0))
      | ~ r2_hidden(X5,X4)
      | r2_orders_2(sK0,X5,sK2(X6,sK0,X4))
      | ~ r2_hidden(X6,a_2_0_orders_2(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f79,f27])).

fof(f79,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X5,k2_struct_0(sK0))
      | ~ r2_hidden(X5,X4)
      | r2_orders_2(sK0,X5,sK2(X6,sK0,X4))
      | ~ r2_hidden(X6,a_2_0_orders_2(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f78,f31])).

fof(f78,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X5,k2_struct_0(sK0))
      | ~ r2_hidden(X5,X4)
      | r2_orders_2(sK0,X5,sK2(X6,sK0,X4))
      | ~ r2_hidden(X6,a_2_0_orders_2(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f77,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X5,k2_struct_0(sK0))
      | ~ r2_hidden(X5,X4)
      | r2_orders_2(sK0,X5,sK2(X6,sK0,X4))
      | ~ r2_hidden(X6,a_2_0_orders_2(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f76,f29])).

fof(f76,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X5,k2_struct_0(sK0))
      | ~ r2_hidden(X5,X4)
      | r2_orders_2(sK0,X5,sK2(X6,sK0,X4))
      | ~ r2_hidden(X6,a_2_0_orders_2(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f62,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X5,k2_struct_0(sK0))
      | ~ r2_hidden(X5,X4)
      | r2_orders_2(sK0,X5,sK2(X6,sK0,X4))
      | ~ r2_hidden(X6,a_2_0_orders_2(sK0,X4)) ) ),
    inference(superposition,[],[f40,f57])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,X4,sK2(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:55:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (690)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (689)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (689)Refutation not found, incomplete strategy% (689)------------------------------
% 0.20/0.52  % (689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (689)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (689)Memory used [KB]: 10618
% 0.20/0.52  % (689)Time elapsed: 0.082 s
% 0.20/0.52  % (689)------------------------------
% 0.20/0.52  % (689)------------------------------
% 0.20/0.52  % (705)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (709)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (703)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (691)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (694)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (693)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (694)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f137,f110])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.20/0.54    inference(forward_demodulation,[],[f109,f103])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f102,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.20/0.54    inference(negated_conjecture,[],[f11])).
% 0.20/0.54  fof(f11,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.54    inference(resolution,[],[f101,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | sK2(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 0.20/0.54    inference(forward_demodulation,[],[f100,f97])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.54    inference(forward_demodulation,[],[f96,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    k1_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))) = a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0)))),
% 0.20/0.54    inference(resolution,[],[f95,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f94,f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ~v2_struct_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f93,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    l1_orders_2(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f92,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    v5_orders_2(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f91,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    v4_orders_2(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f65,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    v3_orders_2(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_orders_2(sK0,X11) = a_2_0_orders_2(sK0,X11)) )),
% 0.20/0.54    inference(superposition,[],[f33,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f55,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    l1_struct_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f31,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0))) | sK2(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 0.20/0.54    inference(forward_demodulation,[],[f99,f49])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ( ! [X0] : (sK2(X0,sK0,k2_struct_0(sK0)) = X0 | ~r2_hidden(X0,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f98,f49])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    ( ! [X0] : (sK2(X0,sK0,k2_subset_1(k2_struct_0(sK0))) = X0 | ~r2_hidden(X0,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))))) )),
% 0.20/0.54    inference(resolution,[],[f90,f44])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | sK2(X10,sK0,X9) = X10 | ~r2_hidden(X10,a_2_0_orders_2(sK0,X9))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f89,f27])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | sK2(X10,sK0,X9) = X10 | ~r2_hidden(X10,a_2_0_orders_2(sK0,X9))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f88,f31])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(X10,sK0,X9) = X10 | ~r2_hidden(X10,a_2_0_orders_2(sK0,X9))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f87,f30])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(X10,sK0,X9) = X10 | ~r2_hidden(X10,a_2_0_orders_2(sK0,X9))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f86,f29])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(X10,sK0,X9) = X10 | ~r2_hidden(X10,a_2_0_orders_2(sK0,X9))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f64,f28])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(X10,sK0,X9) = X10 | ~r2_hidden(X10,a_2_0_orders_2(sK0,X9))) )),
% 0.20/0.54    inference(superposition,[],[f42,f57])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | v2_struct_0(X1) | sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    m1_subset_1(sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f108,f32])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    m1_subset_1(sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.54    inference(resolution,[],[f107,f35])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f106,f97])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f105,f49])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f104,f49])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK2(X0,sK0,k2_subset_1(k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))))) )),
% 0.20/0.54    inference(resolution,[],[f85,f44])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f84,f27])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f83,f31])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f82,f30])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f81,f29])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f63,f28])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(sK2(X8,sK0,X7),k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 0.20/0.54    inference(superposition,[],[f41,f57])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | v2_struct_0(X1) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.20/0.54    inference(forward_demodulation,[],[f136,f57])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f133,f31])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.54    inference(resolution,[],[f132,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.20/0.54    inference(equality_resolution,[],[f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 != X2 | ~r2_orders_2(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.20/0.54  fof(f132,plain,(
% 0.20/0.54    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))),
% 0.20/0.54    inference(forward_demodulation,[],[f131,f103])).
% 0.20/0.54  fof(f131,plain,(
% 0.20/0.54    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f130,f32])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.54    inference(resolution,[],[f129,f35])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK2(X0,sK0,k2_struct_0(sK0)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f128,f116])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f115,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.54    inference(backward_demodulation,[],[f58,f57])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f56,f27])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    v2_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.54    inference(resolution,[],[f55,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    v1_xboole_0(k2_struct_0(sK0)) | r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.20/0.54    inference(resolution,[],[f110,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    ( ! [X0] : (r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK2(X0,sK0,k2_struct_0(sK0))) | ~r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))) )),
% 0.20/0.54    inference(resolution,[],[f125,f110])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f124,f97])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,a_2_0_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f123,f49])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X1,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f122,f49])).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_subset_1(k2_struct_0(sK0)))) | ~r2_hidden(X1,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f121,f49])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k2_subset_1(k2_struct_0(sK0))) | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_subset_1(k2_struct_0(sK0)))) | ~r2_hidden(X1,a_2_0_orders_2(sK0,k2_subset_1(k2_struct_0(sK0))))) )),
% 0.20/0.54    inference(resolution,[],[f80,f44])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X5,k2_struct_0(sK0)) | ~r2_hidden(X5,X4) | r2_orders_2(sK0,X5,sK2(X6,sK0,X4)) | ~r2_hidden(X6,a_2_0_orders_2(sK0,X4))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f79,f27])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_subset_1(X5,k2_struct_0(sK0)) | ~r2_hidden(X5,X4) | r2_orders_2(sK0,X5,sK2(X6,sK0,X4)) | ~r2_hidden(X6,a_2_0_orders_2(sK0,X4))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f78,f31])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X5,k2_struct_0(sK0)) | ~r2_hidden(X5,X4) | r2_orders_2(sK0,X5,sK2(X6,sK0,X4)) | ~r2_hidden(X6,a_2_0_orders_2(sK0,X4))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f77,f30])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X5,k2_struct_0(sK0)) | ~r2_hidden(X5,X4) | r2_orders_2(sK0,X5,sK2(X6,sK0,X4)) | ~r2_hidden(X6,a_2_0_orders_2(sK0,X4))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f76,f29])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X5,k2_struct_0(sK0)) | ~r2_hidden(X5,X4) | r2_orders_2(sK0,X5,sK2(X6,sK0,X4)) | ~r2_hidden(X6,a_2_0_orders_2(sK0,X4))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f62,f28])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X5,k2_struct_0(sK0)) | ~r2_hidden(X5,X4) | r2_orders_2(sK0,X5,sK2(X6,sK0,X4)) | ~r2_hidden(X6,a_2_0_orders_2(sK0,X4))) )),
% 0.20/0.54    inference(superposition,[],[f40,f57])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(X4,X2) | r2_orders_2(X1,X4,sK2(X0,X1,X2)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (694)------------------------------
% 0.20/0.54  % (694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (694)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (694)Memory used [KB]: 6140
% 0.20/0.54  % (694)Time elapsed: 0.115 s
% 0.20/0.54  % (694)------------------------------
% 0.20/0.54  % (694)------------------------------
% 0.20/0.54  % (688)Success in time 0.181 s
%------------------------------------------------------------------------------
