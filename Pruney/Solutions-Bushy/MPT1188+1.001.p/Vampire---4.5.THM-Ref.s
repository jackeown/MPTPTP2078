%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1188+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:26 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  165 (28143 expanded)
%              Number of leaves         :   16 (5174 expanded)
%              Depth                    :   76
%              Number of atoms          :  581 (160546 expanded)
%              Number of equality atoms :   52 (13996 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(subsumption_resolution,[],[f339,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r8_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r8_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r8_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( X1 != X2
                   => r2_orders_2(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r8_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( X1 != X2
                 => r2_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_orders_2)).

fof(f339,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f338,f88])).

fof(f88,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f53,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f53,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f338,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f327,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f327,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f326,f90])).

fof(f90,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f48,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f48,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f326,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f325,f99])).

fof(f99,plain,(
    u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f98,f89])).

fof(f89,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f53,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f98,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f97,f81])).

fof(f81,plain,(
    v1_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f79,f53])).

fof(f79,plain,
    ( ~ l1_orders_2(sK0)
    | v1_relat_2(u1_orders_2(sK0)) ),
    inference(resolution,[],[f50,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_relat_2(u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v1_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_orders_2)).

fof(f50,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,
    ( ~ v1_relat_2(u1_orders_2(sK0))
    | ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f96,f84])).

fof(f84,plain,(
    v8_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f83,f53])).

fof(f83,plain,
    ( ~ l1_orders_2(sK0)
    | v8_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f82,f80])).

fof(f80,plain,(
    v2_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f78,f53])).

fof(f78,plain,
    ( ~ l1_orders_2(sK0)
    | v2_orders_2(sK0) ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
       => v2_orders_2(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_orders_2)).

fof(f82,plain,
    ( ~ v2_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v8_relat_2(u1_orders_2(sK0)) ),
    inference(resolution,[],[f51,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v8_relat_2(u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v2_orders_2(X0) )
     => v8_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_orders_2)).

fof(f51,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,
    ( ~ v8_relat_2(u1_orders_2(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0))
    | ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f95,f87])).

fof(f87,plain,(
    v4_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f86,f53])).

fof(f86,plain,
    ( ~ l1_orders_2(sK0)
    | v4_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f85,f80])).

fof(f85,plain,
    ( ~ v2_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v4_relat_2(u1_orders_2(sK0)) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_relat_2(u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v2_orders_2(X0) )
     => v4_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_orders_2)).

fof(f52,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f95,plain,
    ( ~ v4_relat_2(u1_orders_2(sK0))
    | ~ v8_relat_2(u1_orders_2(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0))
    | ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k3_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v4_relat_2(X1)
        & v1_relat_2(X1) )
     => k3_relat_1(X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_orders_1)).

fof(f92,plain,(
    v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f91,f53])).

fof(f91,plain,
    ( ~ l1_orders_2(sK0)
    | v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f80,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_orders_2(X0) )
     => v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_orders_2)).

fof(f325,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0))) ),
    inference(subsumption_resolution,[],[f324,f241])).

fof(f241,plain,
    ( ~ r8_orders_1(u1_orders_2(sK0),sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f239,f45])).

fof(f45,plain,
    ( ~ r8_orders_1(u1_orders_2(sK0),sK1)
    | sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f239,plain,
    ( sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f232,f46])).

fof(f46,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f232,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    | sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f231,f165])).

fof(f165,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f164,f90])).

fof(f164,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f163,f99])).

fof(f163,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0))) ),
    inference(subsumption_resolution,[],[f162,f44])).

fof(f44,plain,
    ( ~ r8_orders_1(u1_orders_2(sK0),sK1)
    | m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f162,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f160,f100])).

fof(f100,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f89,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f160,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f154,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X1),X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r8_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(X2,k3_relat_1(X0))
               => ( r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2 ) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_1)).

fof(f154,plain,
    ( r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f153,f116])).

fof(f116,plain,
    ( m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f113,f44])).

fof(f113,plain,
    ( r8_orders_1(u1_orders_2(sK0),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f110,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f110,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f105,f90])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
      | r8_orders_1(u1_orders_2(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f102,f100])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ v1_relat_1(u1_orders_2(sK0))
      | r2_hidden(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
      | r8_orders_1(u1_orders_2(sK0),X0) ) ),
    inference(superposition,[],[f58,f99])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k3_relat_1(X0))
      | r8_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f153,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f152,f53])).

fof(f152,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f150,f48])).

fof(f150,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f141,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f141,plain,
    ( r1_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f140,f116])).

fof(f140,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f139,f53])).

fof(f139,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f131,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f131,plain,
    ( r2_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f130,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f127,f108])).

fof(f108,plain,
    ( sK1 != sK3(u1_orders_2(sK0),sK1)
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f106,f90])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK0))
      | sK3(u1_orders_2(sK0),X1) != X1
      | r8_orders_1(u1_orders_2(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f103,f100])).

fof(f103,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ v1_relat_1(u1_orders_2(sK0))
      | sK3(u1_orders_2(sK0),X1) != X1
      | r8_orders_1(u1_orders_2(sK0),X1) ) ),
    inference(superposition,[],[f59,f99])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | sK3(X0,X1) != X1
      | r8_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f127,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),sK1)
    | r2_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f116,f47])).

fof(f47,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | sK1 = X2
      | r2_orders_2(sK0,X2,sK1)
      | r8_orders_1(u1_orders_2(sK0),sK1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f231,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f230,f53])).

fof(f230,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f229,f48])).

fof(f229,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_orders_2(sK0,sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f222,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f222,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f221,f165])).

fof(f221,plain,
    ( sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f220,f53])).

fof(f220,plain,
    ( sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f218,f48])).

fof(f218,plain,
    ( sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f217,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f217,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f216,f165])).

fof(f216,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f215,f173])).

fof(f173,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | sK2 = X0
      | r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK0))
      | ~ r8_orders_1(u1_orders_2(sK0),X0) ) ),
    inference(resolution,[],[f172,f107])).

fof(f107,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,u1_struct_0(sK0))
      | X2 = X3
      | r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | ~ r8_orders_1(u1_orders_2(sK0),X3) ) ),
    inference(subsumption_resolution,[],[f104,f100])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ v1_relat_1(u1_orders_2(sK0))
      | X2 = X3
      | r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | ~ r8_orders_1(u1_orders_2(sK0),X3) ) ),
    inference(superposition,[],[f61,f99])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | X1 = X2
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ r8_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f172,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f165,f74])).

fof(f215,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f214,f53])).

fof(f214,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f211,f48])).

fof(f211,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f196,f71])).

fof(f196,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f195,f165])).

fof(f195,plain,
    ( sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f194,f53])).

fof(f194,plain,
    ( sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f193,f48])).

fof(f193,plain,
    ( sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f170,f54])).

fof(f170,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    | sK1 = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f165,f47])).

fof(f324,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f322,f100])).

fof(f322,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f294,f60])).

fof(f294,plain,
    ( r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f293,f249])).

fof(f249,plain,
    ( m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f241,f113])).

fof(f293,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f292,f53])).

fof(f292,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f290,f48])).

fof(f290,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f283,f71])).

fof(f283,plain,
    ( r1_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f282,f249])).

fof(f282,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f281,f53])).

fof(f281,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f280,f48])).

fof(f280,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f254,f54])).

fof(f254,plain,
    ( r2_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f253,f241])).

fof(f253,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f250,f108])).

fof(f250,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),sK1)
    | r2_orders_2(sK0,sK3(u1_orders_2(sK0),sK1),sK1)
    | r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f249,f47])).

%------------------------------------------------------------------------------
