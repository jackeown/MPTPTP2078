%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 303 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   26
%              Number of atoms          :  357 (1486 expanded)
%              Number of equality atoms :   14 ( 138 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(subsumption_resolution,[],[f232,f81])).

fof(f81,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f42,f80])).

fof(f80,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f51,f79])).

fof(f79,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f42,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f232,plain,(
    k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) ),
    inference(resolution,[],[f227,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f66,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f227,plain,(
    ! [X0] : r1_tarski(k3_orders_2(sK0,k1_xboole_0,sK1),X0) ),
    inference(resolution,[],[f226,f94])).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f226,plain,(
    v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(subsumption_resolution,[],[f224,f49])).

fof(f224,plain,
    ( v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))
    | ~ r1_tarski(k1_xboole_0,sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1))) ),
    inference(resolution,[],[f221,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f221,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0)
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(subsumption_resolution,[],[f220,f161])).

fof(f161,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(subsumption_resolution,[],[f160,f119])).

fof(f119,plain,(
    m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f118,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k3_orders_2(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f117,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f115,f46])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f45,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f113,f44])).

fof(f44,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f71,f47])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f160,plain,
    ( v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))
    | m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))
    | m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(resolution,[],[f123,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m2_subset_1(sK3(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f63,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m2_subset_1(sK3(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ? [X2] : m2_subset_1(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_subset_1)).

fof(f123,plain,(
    ! [X2] :
      ( ~ m2_subset_1(X2,u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1))
      | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))
      | m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f119,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X0) ) ),
    inference(subsumption_resolution,[],[f60,f53])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
         => m1_subset_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_subset_1)).

fof(f220,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0)
    | ~ m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(subsumption_resolution,[],[f219,f50])).

fof(f219,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0)
    | ~ m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(subsumption_resolution,[],[f217,f41])).

fof(f217,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0)
    | ~ m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(resolution,[],[f150,f192])).

fof(f192,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))
    | r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(resolution,[],[f189,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f189,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(subsumption_resolution,[],[f188,f119])).

fof(f188,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))
    | ~ m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))
    | ~ m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ),
    inference(resolution,[],[f122,f78])).

fof(f122,plain,(
    ! [X1] :
      ( ~ m2_subset_1(X1,u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1))
      | m1_subset_1(X1,k3_orders_2(sK0,k1_xboole_0,sK1))
      | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) ) ),
    inference(resolution,[],[f119,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f62,f53])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f149,f43])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f148,f46])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f147,f45])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f146,f44])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(resolution,[],[f55,f47])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (22878)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.49  % (22887)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (22880)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (22881)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (22885)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (22875)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (22886)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (22899)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (22882)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (22877)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (22891)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (22877)Refutation not found, incomplete strategy% (22877)------------------------------
% 0.20/0.53  % (22877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22877)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (22877)Memory used [KB]: 10746
% 0.20/0.53  % (22877)Time elapsed: 0.125 s
% 0.20/0.53  % (22877)------------------------------
% 0.20/0.53  % (22877)------------------------------
% 0.20/0.54  % (22882)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f235,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f232,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1)),
% 0.20/0.54    inference(backward_demodulation,[],[f42,f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    k1_xboole_0 = k1_struct_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f51,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    l1_struct_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f52,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    l1_orders_2(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.20/0.54    inference(negated_conjecture,[],[f18])).
% 0.20/0.54  fof(f18,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)),
% 0.20/0.54    inference(resolution,[],[f227,f99])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f66,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k3_orders_2(sK0,k1_xboole_0,sK1),X0)) )),
% 0.20/0.54    inference(resolution,[],[f226,f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~v1_xboole_0(X2) | r1_tarski(X2,X3)) )),
% 0.20/0.54    inference(resolution,[],[f68,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f226,plain,(
% 0.20/0.54    v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f224,f49])).
% 0.20/0.54  fof(f224,plain,(
% 0.20/0.54    v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) | ~r1_tarski(k1_xboole_0,sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)))),
% 0.20/0.54    inference(resolution,[],[f221,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.54  fof(f221,plain,(
% 0.20/0.54    r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f220,f161])).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f160,f119])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    inference(resolution,[],[f118,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k3_orders_2(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.54    inference(resolution,[],[f117,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f116,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ~v2_struct_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f115,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    v5_orders_2(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f114,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    v4_orders_2(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f113,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    v3_orders_2(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.54    inference(resolution,[],[f71,f47])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) | m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f159])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) | m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(resolution,[],[f123,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m2_subset_1(sK3(X0,X1),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f63,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m2_subset_1(sK3(X0,X1),X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1] : (? [X2] : m2_subset_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : (? [X2] : m2_subset_1(X2,X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ? [X2] : m2_subset_1(X2,X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_subset_1)).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    ( ! [X2] : (~m2_subset_1(X2,u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) | m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.20/0.54    inference(resolution,[],[f119,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m2_subset_1(X2,X0,X1) | m1_subset_1(X2,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f60,f53])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m2_subset_1(X2,X0,X1) | m1_subset_1(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,X0) | ~m2_subset_1(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,X0) | ~m2_subset_1(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) => m1_subset_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_subset_1)).
% 0.20/0.54  fof(f220,plain,(
% 0.20/0.54    r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0) | ~m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f219,f50])).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0) | ~m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f217,f41])).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0) | ~m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(resolution,[],[f150,f192])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f191])).
% 0.20/0.54  fof(f191,plain,(
% 0.20/0.54    v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) | r2_hidden(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(resolution,[],[f189,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f188,f119])).
% 0.20/0.54  fof(f188,plain,(
% 0.20/0.54    m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) | ~m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f187])).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    m1_subset_1(sK3(u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k3_orders_2(sK0,k1_xboole_0,sK1)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1)) | ~m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))),
% 0.20/0.54    inference(resolution,[],[f122,f78])).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X1] : (~m2_subset_1(X1,u1_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)) | m1_subset_1(X1,k3_orders_2(sK0,k1_xboole_0,sK1)) | v1_xboole_0(k3_orders_2(sK0,k1_xboole_0,sK1))) )),
% 0.20/0.54    inference(resolution,[],[f119,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f62,f53])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f149,f43])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f148,f46])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f147,f45])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f146,f44])).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.20/0.54    inference(resolution,[],[f55,f47])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (22882)------------------------------
% 0.20/0.54  % (22882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22882)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (22882)Memory used [KB]: 6396
% 0.20/0.54  % (22882)Time elapsed: 0.129 s
% 0.20/0.54  % (22882)------------------------------
% 0.20/0.54  % (22882)------------------------------
% 0.20/0.54  % (22876)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (22901)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (22895)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (22884)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (22905)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (22872)Success in time 0.183 s
%------------------------------------------------------------------------------
