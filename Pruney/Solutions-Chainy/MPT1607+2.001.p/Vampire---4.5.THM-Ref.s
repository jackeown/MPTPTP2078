%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:35 EST 2020

% Result     : Theorem 3.24s
% Output     : Refutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  142 (1248 expanded)
%              Number of leaves         :   16 ( 295 expanded)
%              Depth                    :   39
%              Number of atoms          :  461 (2985 expanded)
%              Number of equality atoms :   55 ( 717 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1572,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1146,f42])).

fof(f42,plain,(
    ~ r2_hidden(k3_tarski(sK0),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      & v2_yellow_0(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      & v2_yellow_0(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_yellow_0(k2_yellow_1(X0))
         => r2_hidden(k3_tarski(X0),X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_yellow_0(k2_yellow_1(X0))
       => r2_hidden(k3_tarski(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_1)).

fof(f1146,plain,(
    r2_hidden(k3_tarski(sK0),sK0) ),
    inference(backward_demodulation,[],[f408,f1145])).

fof(f1145,plain,(
    k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f1144,f40])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1144,plain,
    ( k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f1143,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f43,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f1143,plain,
    ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f1131,f987])).

fof(f987,plain,
    ( r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(factoring,[],[f866])).

fof(f866,plain,(
    ! [X4] :
      ( r2_hidden(sK4(sK0,X4),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | r2_hidden(sK4(sK0,X4),X4)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | k3_tarski(sK0) = X4 ) ),
    inference(resolution,[],[f860,f240])).

fof(f240,plain,(
    ! [X14,X12,X13] :
      ( ~ r1_tarski(k3_tarski(X12),X14)
      | k3_tarski(X12) = X13
      | r2_hidden(sK4(X12,X13),X14)
      | r2_hidden(sK4(X12,X13),X13) ) ),
    inference(resolution,[],[f220,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f220,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),k3_tarski(X0))
      | k3_tarski(X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),k3_tarski(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(resolution,[],[f117,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),sK6(X0,X1))
      | r2_hidden(sK4(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK6(X0,X1))
      | k3_tarski(X0) = X1
      | r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(resolution,[],[f70,f85])).

fof(f85,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f860,plain,
    ( r1_tarski(k3_tarski(sK0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f859])).

fof(f859,plain,
    ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | r1_tarski(k3_tarski(sK0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k3_tarski(sK0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(resolution,[],[f814,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f814,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK3(X7,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_tarski(sK0))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | r1_tarski(X7,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(resolution,[],[f808,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f808,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ r2_hidden(X0,k3_tarski(sK0))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f801])).

fof(f801,plain,(
    ! [X0] :
      ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(X0,k3_tarski(sK0))
      | r2_hidden(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ r2_hidden(X0,k3_tarski(sK0)) ) ),
    inference(resolution,[],[f789,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK5(X1,X0),X2)
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f87,f65])).

fof(f87,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK5(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK5(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f789,plain,(
    ! [X1] :
      ( r1_tarski(sK5(sK0,X1),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(X1,k3_tarski(sK0)) ) ),
    inference(resolution,[],[f784,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK5(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f784,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | r1_tarski(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(subsumption_resolution,[],[f783,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f783,plain,(
    ! [X0] :
      ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | r1_tarski(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(subsumption_resolution,[],[f782,f457])).

fof(f457,plain,(
    m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) ),
    inference(resolution,[],[f449,f76])).

fof(f76,plain,(
    v2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f41,plain,(
    v2_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f449,plain,(
    ! [X4] :
      ( ~ v2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)))
      | m1_subset_1(sK1(g1_orders_2(X4,k1_yellow_1(X4))),X4) ) ),
    inference(subsumption_resolution,[],[f446,f79])).

fof(f79,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f48,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f446,plain,(
    ! [X4] :
      ( m1_subset_1(sK1(g1_orders_2(X4,k1_yellow_1(X4))),X4)
      | ~ l1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)))
      | ~ v2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4))) ) ),
    inference(superposition,[],[f54,f374])).

fof(f374,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[],[f373])).

fof(f373,plain,(
    ! [X4,X3] :
      ( g1_orders_2(X3,k1_yellow_1(X3)) != g1_orders_2(X4,k1_yellow_1(X4))
      | u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))) = X4 ) ),
    inference(resolution,[],[f136,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f136,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7)))
      | g1_orders_2(X6,k1_yellow_1(X6)) != g1_orders_2(X7,X8)
      | u1_struct_0(g1_orders_2(X6,k1_yellow_1(X6))) = X7 ) ),
    inference(superposition,[],[f63,f100])).

fof(f100,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ),
    inference(subsumption_resolution,[],[f99,f79])).

fof(f99,plain,(
    ! [X0] :
      ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f45,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_0)).

fof(f782,plain,(
    ! [X0] :
      ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | r1_tarski(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) ) ),
    inference(subsumption_resolution,[],[f779,f40])).

fof(f779,plain,(
    ! [X0] :
      ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | r1_tarski(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) ) ),
    inference(resolution,[],[f778,f400])).

fof(f400,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f375,f374])).

fof(f375,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) ) ),
    inference(backward_demodulation,[],[f83,f374])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) ) ),
    inference(definition_unfolding,[],[f52,f43,f43,f43])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f778,plain,(
    ! [X1] :
      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f777,f457])).

fof(f777,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
      | ~ r2_hidden(X1,sK0)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(forward_demodulation,[],[f776,f374])).

fof(f776,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(subsumption_resolution,[],[f775,f61])).

fof(f775,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ r2_hidden(X1,sK0)
      | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(forward_demodulation,[],[f774,f374])).

fof(f774,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(subsumption_resolution,[],[f773,f79])).

fof(f773,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(subsumption_resolution,[],[f769,f77])).

fof(f77,plain,(
    ! [X0] : v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f46,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f769,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(resolution,[],[f763,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f763,plain,(
    ! [X0] :
      ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f762,f61])).

fof(f762,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f760,f457])).

fof(f760,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
      | ~ r2_hidden(X0,sK0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f403,f470])).

fof(f470,plain,(
    r2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(resolution,[],[f448,f76])).

fof(f448,plain,(
    ! [X3] :
      ( ~ v2_yellow_0(g1_orders_2(X3,k1_yellow_1(X3)))
      | r2_lattice3(g1_orders_2(X3,k1_yellow_1(X3)),X3,sK1(g1_orders_2(X3,k1_yellow_1(X3)))) ) ),
    inference(subsumption_resolution,[],[f445,f79])).

fof(f445,plain,(
    ! [X3] :
      ( r2_lattice3(g1_orders_2(X3,k1_yellow_1(X3)),X3,sK1(g1_orders_2(X3,k1_yellow_1(X3))))
      | ~ l1_orders_2(g1_orders_2(X3,k1_yellow_1(X3)))
      | ~ v2_yellow_0(g1_orders_2(X3,k1_yellow_1(X3))) ) ),
    inference(superposition,[],[f55,f374])).

fof(f55,plain,(
    ! [X0] :
      ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f403,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X3,X0)
      | ~ m1_subset_1(X0,X1)
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0)
      | ~ m1_subset_1(X2,X1) ) ),
    inference(forward_demodulation,[],[f380,f374])).

fof(f380,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0)
      | ~ r2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X3,X0) ) ),
    inference(backward_demodulation,[],[f189,f374])).

fof(f189,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0)
      | ~ r2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X3,X0) ) ),
    inference(resolution,[],[f57,f79])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f1131,plain,
    ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(resolution,[],[f855,f408])).

fof(f855,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),X0) ) ),
    inference(subsumption_resolution,[],[f854,f408])).

fof(f854,plain,(
    ! [X0] :
      ( k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),X0) ) ),
    inference(duplicate_literal_removal,[],[f847])).

fof(f847,plain,(
    ! [X0] :
      ( k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),X0)
      | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f846,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK4(X0,X1),X3)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f846,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | k3_tarski(sK0) = X0
      | ~ r2_hidden(X0,sK0)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f845,f68])).

fof(f845,plain,(
    ! [X0] :
      ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | k3_tarski(sK0) = X0
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(sK4(sK0,X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | r2_hidden(sK4(sK0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f838])).

fof(f838,plain,(
    ! [X0] :
      ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | k3_tarski(sK0) = X0
      | ~ r2_hidden(X0,sK0)
      | k3_tarski(sK0) = X0
      | r2_hidden(sK4(sK0,X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | r2_hidden(sK4(sK0,X0),X0) ) ),
    inference(resolution,[],[f790,f133])).

fof(f133,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK6(X3,X4),X5)
      | k3_tarski(X3) = X4
      | r2_hidden(sK4(X3,X4),X5)
      | r2_hidden(sK4(X3,X4),X4) ) ),
    inference(resolution,[],[f69,f65])).

fof(f790,plain,(
    ! [X2] :
      ( r1_tarski(sK6(sK0,X2),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | k3_tarski(sK0) = X2
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f784,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1,X0),X1)
      | k3_tarski(X1) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k3_tarski(X1) = X0
      | r2_hidden(sK6(X1,X0),X1)
      | r2_hidden(sK6(X1,X0),X1)
      | k3_tarski(X1) = X0 ) ),
    inference(resolution,[],[f161,f70])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X1,X2),X0)
      | ~ r2_hidden(X0,X1)
      | k3_tarski(X1) = X2
      | r2_hidden(sK6(X1,X2),X1) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(sK4(X1,X2),X0)
      | k3_tarski(X1) = X2
      | r2_hidden(sK6(X1,X2),X1)
      | k3_tarski(X1) = X2 ) ),
    inference(resolution,[],[f68,f70])).

fof(f408,plain,(
    r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) ),
    inference(forward_demodulation,[],[f407,f374])).

fof(f407,plain,(
    r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(subsumption_resolution,[],[f386,f40])).

fof(f386,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(backward_demodulation,[],[f105,f374])).

fof(f105,plain,
    ( r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v1_xboole_0(u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(subsumption_resolution,[],[f104,f79])).

fof(f104,plain,
    ( ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(resolution,[],[f92,f76])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_hidden(sK1(X0),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (5816)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.51  % (5820)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.53  % (5827)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.53  % (5824)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.55  % (5815)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.55  % (5825)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.55  % (5821)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.56  % (5812)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.57  % (5834)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.57  % (5841)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.57  % (5826)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.57  % (5838)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.57  % (5836)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.57  % (5839)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.58  % (5813)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.58  % (5832)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.58  % (5818)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.58  % (5832)Refutation not found, incomplete strategy% (5832)------------------------------
% 1.33/0.58  % (5832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.58  % (5832)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.58  
% 1.33/0.58  % (5832)Memory used [KB]: 10746
% 1.33/0.58  % (5832)Time elapsed: 0.178 s
% 1.33/0.58  % (5832)------------------------------
% 1.33/0.58  % (5832)------------------------------
% 1.33/0.58  % (5831)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.58  % (5840)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.59  % (5823)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.59  % (5829)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.59  % (5838)Refutation not found, incomplete strategy% (5838)------------------------------
% 1.33/0.59  % (5838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.59  % (5838)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.59  
% 1.33/0.59  % (5838)Memory used [KB]: 10746
% 1.33/0.59  % (5838)Time elapsed: 0.169 s
% 1.33/0.59  % (5838)------------------------------
% 1.33/0.59  % (5838)------------------------------
% 1.33/0.59  % (5833)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.59  % (5811)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.60  % (5833)Refutation not found, incomplete strategy% (5833)------------------------------
% 1.33/0.60  % (5833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.60  % (5833)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.60  
% 1.33/0.60  % (5833)Memory used [KB]: 1791
% 1.33/0.60  % (5833)Time elapsed: 0.161 s
% 1.33/0.60  % (5833)------------------------------
% 1.33/0.60  % (5833)------------------------------
% 1.33/0.62  % (5814)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 2.08/0.62  % (5822)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.08/0.63  % (5822)Refutation not found, incomplete strategy% (5822)------------------------------
% 2.08/0.63  % (5822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (5822)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.63  
% 2.08/0.63  % (5822)Memory used [KB]: 10618
% 2.08/0.63  % (5822)Time elapsed: 0.190 s
% 2.08/0.63  % (5822)------------------------------
% 2.08/0.63  % (5822)------------------------------
% 2.08/0.63  % (5835)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.08/0.63  % (5837)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.08/0.64  % (5828)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.08/0.64  % (5830)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.08/0.64  % (5819)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.54/0.73  % (5868)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.07/0.80  % (5866)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.24/0.83  % (5818)Refutation found. Thanks to Tanya!
% 3.24/0.83  % SZS status Theorem for theBenchmark
% 3.24/0.83  % SZS output start Proof for theBenchmark
% 3.24/0.83  fof(f1572,plain,(
% 3.24/0.83    $false),
% 3.24/0.83    inference(subsumption_resolution,[],[f1146,f42])).
% 3.24/0.83  fof(f42,plain,(
% 3.24/0.83    ~r2_hidden(k3_tarski(sK0),sK0)),
% 3.24/0.83    inference(cnf_transformation,[],[f25])).
% 3.24/0.83  fof(f25,plain,(
% 3.24/0.83    ? [X0] : (~r2_hidden(k3_tarski(X0),X0) & v2_yellow_0(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 3.24/0.83    inference(flattening,[],[f24])).
% 3.24/0.83  fof(f24,plain,(
% 3.24/0.83    ? [X0] : ((~r2_hidden(k3_tarski(X0),X0) & v2_yellow_0(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 3.24/0.83    inference(ennf_transformation,[],[f17])).
% 3.24/0.83  fof(f17,negated_conjecture,(
% 3.24/0.83    ~! [X0] : (~v1_xboole_0(X0) => (v2_yellow_0(k2_yellow_1(X0)) => r2_hidden(k3_tarski(X0),X0)))),
% 3.24/0.83    inference(negated_conjecture,[],[f16])).
% 3.42/0.83  fof(f16,conjecture,(
% 3.42/0.83    ! [X0] : (~v1_xboole_0(X0) => (v2_yellow_0(k2_yellow_1(X0)) => r2_hidden(k3_tarski(X0),X0)))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_1)).
% 3.42/0.83  fof(f1146,plain,(
% 3.42/0.83    r2_hidden(k3_tarski(sK0),sK0)),
% 3.42/0.83    inference(backward_demodulation,[],[f408,f1145])).
% 3.42/0.83  fof(f1145,plain,(
% 3.42/0.83    k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 3.42/0.83    inference(subsumption_resolution,[],[f1144,f40])).
% 3.42/0.83  fof(f40,plain,(
% 3.42/0.83    ~v1_xboole_0(sK0)),
% 3.42/0.83    inference(cnf_transformation,[],[f25])).
% 3.42/0.83  fof(f1144,plain,(
% 3.42/0.83    k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) | v1_xboole_0(sK0)),
% 3.42/0.83    inference(resolution,[],[f1143,f82])).
% 3.42/0.83  fof(f82,plain,(
% 3.42/0.83    ( ! [X0] : (~v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.42/0.83    inference(definition_unfolding,[],[f49,f43])).
% 3.42/0.83  fof(f43,plain,(
% 3.42/0.83    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 3.42/0.83    inference(cnf_transformation,[],[f10])).
% 3.42/0.83  fof(f10,axiom,(
% 3.42/0.83    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).
% 3.42/0.83  fof(f49,plain,(
% 3.42/0.83    ( ! [X0] : (v1_xboole_0(X0) | ~v2_struct_0(k2_yellow_1(X0))) )),
% 3.42/0.83    inference(cnf_transformation,[],[f26])).
% 3.42/0.83  fof(f26,plain,(
% 3.42/0.83    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 3.42/0.83    inference(ennf_transformation,[],[f14])).
% 3.42/0.83  fof(f14,axiom,(
% 3.42/0.83    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 3.42/0.83  fof(f1143,plain,(
% 3.42/0.83    v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 3.42/0.83    inference(subsumption_resolution,[],[f1131,f987])).
% 3.42/0.83  fof(f987,plain,(
% 3.42/0.83    r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 3.42/0.83    inference(factoring,[],[f866])).
% 3.42/0.83  fof(f866,plain,(
% 3.42/0.83    ( ! [X4] : (r2_hidden(sK4(sK0,X4),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r2_hidden(sK4(sK0,X4),X4) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k3_tarski(sK0) = X4) )),
% 3.42/0.83    inference(resolution,[],[f860,f240])).
% 3.42/0.83  fof(f240,plain,(
% 3.42/0.83    ( ! [X14,X12,X13] : (~r1_tarski(k3_tarski(X12),X14) | k3_tarski(X12) = X13 | r2_hidden(sK4(X12,X13),X14) | r2_hidden(sK4(X12,X13),X13)) )),
% 3.42/0.83    inference(resolution,[],[f220,f65])).
% 3.42/0.83  fof(f65,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f37])).
% 3.42/0.83  fof(f37,plain,(
% 3.42/0.83    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.42/0.83    inference(ennf_transformation,[],[f1])).
% 3.42/0.83  fof(f1,axiom,(
% 3.42/0.83    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.42/0.83  fof(f220,plain,(
% 3.42/0.83    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),k3_tarski(X0)) | k3_tarski(X0) = X1) )),
% 3.42/0.83    inference(duplicate_literal_removal,[],[f214])).
% 3.42/0.83  fof(f214,plain,(
% 3.42/0.83    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),k3_tarski(X0)) | r2_hidden(sK4(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 3.42/0.83    inference(resolution,[],[f117,f69])).
% 3.42/0.83  fof(f69,plain,(
% 3.42/0.83    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),sK6(X0,X1)) | r2_hidden(sK4(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 3.42/0.83    inference(cnf_transformation,[],[f2])).
% 3.42/0.83  fof(f2,axiom,(
% 3.42/0.83    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 3.42/0.83  fof(f117,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (~r2_hidden(X2,sK6(X0,X1)) | k3_tarski(X0) = X1 | r2_hidden(sK4(X0,X1),X1) | r2_hidden(X2,k3_tarski(X0))) )),
% 3.42/0.83    inference(resolution,[],[f70,f85])).
% 3.42/0.83  fof(f85,plain,(
% 3.42/0.83    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3) | r2_hidden(X2,k3_tarski(X0))) )),
% 3.42/0.83    inference(equality_resolution,[],[f73])).
% 3.42/0.83  fof(f73,plain,(
% 3.42/0.83    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 3.42/0.83    inference(cnf_transformation,[],[f2])).
% 3.42/0.83  fof(f70,plain,(
% 3.42/0.83    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 3.42/0.83    inference(cnf_transformation,[],[f2])).
% 3.42/0.83  fof(f860,plain,(
% 3.42/0.83    r1_tarski(k3_tarski(sK0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 3.42/0.83    inference(duplicate_literal_removal,[],[f859])).
% 3.42/0.83  fof(f859,plain,(
% 3.42/0.83    v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r1_tarski(k3_tarski(sK0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r1_tarski(k3_tarski(sK0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.42/0.83    inference(resolution,[],[f814,f66])).
% 3.42/0.83  fof(f66,plain,(
% 3.42/0.83    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f37])).
% 3.42/0.83  fof(f814,plain,(
% 3.42/0.83    ( ! [X7] : (~r2_hidden(sK3(X7,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_tarski(sK0)) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r1_tarski(X7,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(resolution,[],[f808,f67])).
% 3.42/0.83  fof(f67,plain,(
% 3.42/0.83    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f37])).
% 3.42/0.83  fof(f808,plain,(
% 3.42/0.83    ( ! [X0] : (r2_hidden(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r2_hidden(X0,k3_tarski(sK0)) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.42/0.83    inference(duplicate_literal_removal,[],[f801])).
% 3.42/0.83  fof(f801,plain,(
% 3.42/0.83    ( ! [X0] : (v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(X0,k3_tarski(sK0)) | r2_hidden(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r2_hidden(X0,k3_tarski(sK0))) )),
% 3.42/0.83    inference(resolution,[],[f789,f95])).
% 3.42/0.83  fof(f95,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (~r1_tarski(sK5(X1,X0),X2) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_tarski(X1))) )),
% 3.42/0.83    inference(resolution,[],[f87,f65])).
% 3.42/0.83  fof(f87,plain,(
% 3.42/0.83    ( ! [X2,X0] : (r2_hidden(X2,sK5(X0,X2)) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 3.42/0.83    inference(equality_resolution,[],[f71])).
% 3.42/0.83  fof(f71,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (r2_hidden(X2,sK5(X0,X2)) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 3.42/0.83    inference(cnf_transformation,[],[f2])).
% 3.42/0.83  fof(f789,plain,(
% 3.42/0.83    ( ! [X1] : (r1_tarski(sK5(sK0,X1),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(X1,k3_tarski(sK0))) )),
% 3.42/0.83    inference(resolution,[],[f784,f86])).
% 3.42/0.83  fof(f86,plain,(
% 3.42/0.83    ( ! [X2,X0] : (r2_hidden(sK5(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 3.42/0.83    inference(equality_resolution,[],[f72])).
% 3.42/0.83  fof(f72,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X2),X0) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 3.42/0.83    inference(cnf_transformation,[],[f2])).
% 3.42/0.83  fof(f784,plain,(
% 3.42/0.83    ( ! [X0] : (~r2_hidden(X0,sK0) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r1_tarski(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f783,f61])).
% 3.42/0.83  fof(f61,plain,(
% 3.42/0.83    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f33])).
% 3.42/0.83  fof(f33,plain,(
% 3.42/0.83    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.42/0.83    inference(ennf_transformation,[],[f3])).
% 3.42/0.83  fof(f3,axiom,(
% 3.42/0.83    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 3.42/0.83  fof(f783,plain,(
% 3.42/0.83    ( ! [X0] : (v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0) | r1_tarski(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f782,f457])).
% 3.42/0.83  fof(f457,plain,(
% 3.42/0.83    m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)),
% 3.42/0.83    inference(resolution,[],[f449,f76])).
% 3.42/0.83  fof(f76,plain,(
% 3.42/0.83    v2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 3.42/0.83    inference(definition_unfolding,[],[f41,f43])).
% 3.42/0.83  fof(f41,plain,(
% 3.42/0.83    v2_yellow_0(k2_yellow_1(sK0))),
% 3.42/0.83    inference(cnf_transformation,[],[f25])).
% 3.42/0.83  fof(f449,plain,(
% 3.42/0.83    ( ! [X4] : (~v2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4))) | m1_subset_1(sK1(g1_orders_2(X4,k1_yellow_1(X4))),X4)) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f446,f79])).
% 3.42/0.83  fof(f79,plain,(
% 3.42/0.83    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.42/0.83    inference(definition_unfolding,[],[f48,f43])).
% 3.42/0.83  fof(f48,plain,(
% 3.42/0.83    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.42/0.83    inference(cnf_transformation,[],[f12])).
% 3.42/0.83  fof(f12,axiom,(
% 3.42/0.83    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 3.42/0.83  fof(f446,plain,(
% 3.42/0.83    ( ! [X4] : (m1_subset_1(sK1(g1_orders_2(X4,k1_yellow_1(X4))),X4) | ~l1_orders_2(g1_orders_2(X4,k1_yellow_1(X4))) | ~v2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)))) )),
% 3.42/0.83    inference(superposition,[],[f54,f374])).
% 3.42/0.83  fof(f374,plain,(
% 3.42/0.83    ( ! [X0] : (u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0) )),
% 3.42/0.83    inference(equality_resolution,[],[f373])).
% 3.42/0.83  fof(f373,plain,(
% 3.42/0.83    ( ! [X4,X3] : (g1_orders_2(X3,k1_yellow_1(X3)) != g1_orders_2(X4,k1_yellow_1(X4)) | u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))) = X4) )),
% 3.42/0.83    inference(resolution,[],[f136,f44])).
% 3.42/0.83  fof(f44,plain,(
% 3.42/0.83    ( ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.42/0.83    inference(cnf_transformation,[],[f23])).
% 3.42/0.83  fof(f23,plain,(
% 3.42/0.83    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.42/0.83    inference(pure_predicate_removal,[],[f22])).
% 3.42/0.83  fof(f22,plain,(
% 3.42/0.83    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_relat_2(k1_yellow_1(X0)))),
% 3.42/0.83    inference(pure_predicate_removal,[],[f21])).
% 3.42/0.83  fof(f21,plain,(
% 3.42/0.83    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 3.42/0.83    inference(pure_predicate_removal,[],[f20])).
% 3.42/0.83  fof(f20,plain,(
% 3.42/0.83    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 3.42/0.83    inference(pure_predicate_removal,[],[f11])).
% 3.42/0.83  fof(f11,axiom,(
% 3.42/0.83    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k1_yellow_1(X0),X0) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).
% 3.42/0.83  fof(f136,plain,(
% 3.42/0.83    ( ! [X6,X8,X7] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) | g1_orders_2(X6,k1_yellow_1(X6)) != g1_orders_2(X7,X8) | u1_struct_0(g1_orders_2(X6,k1_yellow_1(X6))) = X7) )),
% 3.42/0.83    inference(superposition,[],[f63,f100])).
% 3.42/0.83  fof(f100,plain,(
% 3.42/0.83    ( ! [X0] : (g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))))) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f99,f79])).
% 3.42/0.83  fof(f99,plain,(
% 3.42/0.83    ( ! [X0] : (~l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) | g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))))) )),
% 3.42/0.83    inference(resolution,[],[f53,f78])).
% 3.42/0.83  fof(f78,plain,(
% 3.42/0.83    ( ! [X0] : (v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.42/0.83    inference(definition_unfolding,[],[f45,f43])).
% 3.42/0.83  fof(f45,plain,(
% 3.42/0.83    ( ! [X0] : (v1_orders_2(k2_yellow_1(X0))) )),
% 3.42/0.83    inference(cnf_transformation,[],[f19])).
% 3.42/0.83  fof(f19,plain,(
% 3.42/0.83    ! [X0] : (v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.42/0.83    inference(pure_predicate_removal,[],[f18])).
% 3.42/0.83  fof(f18,plain,(
% 3.42/0.83    ! [X0] : (v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.42/0.83    inference(pure_predicate_removal,[],[f13])).
% 3.42/0.83  fof(f13,axiom,(
% 3.42/0.83    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 3.42/0.83  fof(f53,plain,(
% 3.42/0.83    ( ! [X0] : (~v1_orders_2(X0) | ~l1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0) )),
% 3.42/0.83    inference(cnf_transformation,[],[f29])).
% 3.42/0.83  fof(f29,plain,(
% 3.42/0.83    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 3.42/0.83    inference(flattening,[],[f28])).
% 3.42/0.83  fof(f28,plain,(
% 3.42/0.83    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 3.42/0.83    inference(ennf_transformation,[],[f5])).
% 3.42/0.83  fof(f5,axiom,(
% 3.42/0.83    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 3.42/0.83  fof(f63,plain,(
% 3.42/0.83    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | X0 = X2) )),
% 3.42/0.83    inference(cnf_transformation,[],[f36])).
% 3.42/0.83  fof(f36,plain,(
% 3.42/0.83    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.42/0.83    inference(ennf_transformation,[],[f6])).
% 3.42/0.83  fof(f6,axiom,(
% 3.42/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).
% 3.42/0.83  fof(f54,plain,(
% 3.42/0.83    ( ! [X0] : (m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_yellow_0(X0)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f30])).
% 3.42/0.83  fof(f30,plain,(
% 3.42/0.83    ! [X0] : ((v2_yellow_0(X0) <=> ? [X1] : (r2_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.42/0.83    inference(ennf_transformation,[],[f9])).
% 3.42/0.83  fof(f9,axiom,(
% 3.42/0.83    ! [X0] : (l1_orders_2(X0) => (v2_yellow_0(X0) <=> ? [X1] : (r2_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_0)).
% 3.42/0.83  fof(f782,plain,(
% 3.42/0.83    ( ! [X0] : (v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0) | r1_tarski(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f779,f40])).
% 3.42/0.83  fof(f779,plain,(
% 3.42/0.83    ( ! [X0] : (v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0) | r1_tarski(X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)) )),
% 3.42/0.83    inference(resolution,[],[f778,f400])).
% 3.42/0.83  fof(f400,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 3.42/0.83    inference(forward_demodulation,[],[f375,f374])).
% 3.42/0.83  fof(f375,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_tarski(X1,X2) | ~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)) )),
% 3.42/0.83    inference(backward_demodulation,[],[f83,f374])).
% 3.42/0.83  fof(f83,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_tarski(X1,X2) | ~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)) )),
% 3.42/0.83    inference(definition_unfolding,[],[f52,f43,f43,f43])).
% 3.42/0.83  fof(f52,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f27])).
% 3.42/0.83  fof(f27,plain,(
% 3.42/0.83    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.42/0.83    inference(ennf_transformation,[],[f15])).
% 3.42/0.83  fof(f15,axiom,(
% 3.42/0.83    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 3.42/0.83  fof(f778,plain,(
% 3.42/0.83    ( ! [X1] : (r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(X1,sK0)) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f777,f457])).
% 3.42/0.83  fof(f777,plain,(
% 3.42/0.83    ( ! [X1] : (~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r2_hidden(X1,sK0) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(forward_demodulation,[],[f776,f374])).
% 3.42/0.83  fof(f776,plain,(
% 3.42/0.83    ( ! [X1] : (~r2_hidden(X1,sK0) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f775,f61])).
% 3.42/0.83  fof(f775,plain,(
% 3.42/0.83    ( ! [X1] : (~m1_subset_1(X1,sK0) | ~r2_hidden(X1,sK0) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(forward_demodulation,[],[f774,f374])).
% 3.42/0.83  fof(f774,plain,(
% 3.42/0.83    ( ! [X1] : (~r2_hidden(X1,sK0) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f773,f79])).
% 3.42/0.83  fof(f773,plain,(
% 3.42/0.83    ( ! [X1] : (~r2_hidden(X1,sK0) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f769,f77])).
% 3.42/0.83  fof(f77,plain,(
% 3.42/0.83    ( ! [X0] : (v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.42/0.83    inference(definition_unfolding,[],[f46,f43])).
% 3.42/0.83  fof(f46,plain,(
% 3.42/0.83    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.42/0.83    inference(cnf_transformation,[],[f19])).
% 3.42/0.83  fof(f769,plain,(
% 3.42/0.83    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 3.42/0.83    inference(resolution,[],[f763,f74])).
% 3.42/0.83  fof(f74,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f39])).
% 3.42/0.83  fof(f39,plain,(
% 3.42/0.83    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.42/0.83    inference(flattening,[],[f38])).
% 3.42/0.83  fof(f38,plain,(
% 3.42/0.83    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.42/0.83    inference(ennf_transformation,[],[f7])).
% 3.42/0.83  fof(f7,axiom,(
% 3.42/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 3.42/0.83  fof(f763,plain,(
% 3.42/0.83    ( ! [X0] : (r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r2_hidden(X0,sK0)) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f762,f61])).
% 3.42/0.83  fof(f762,plain,(
% 3.42/0.83    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X0,sK0)) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f760,f457])).
% 3.42/0.83  fof(f760,plain,(
% 3.42/0.83    ( ! [X0] : (~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r2_hidden(X0,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X0,sK0)) )),
% 3.42/0.83    inference(resolution,[],[f403,f470])).
% 3.42/0.83  fof(f470,plain,(
% 3.42/0.83    r2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.42/0.83    inference(resolution,[],[f448,f76])).
% 3.42/0.83  fof(f448,plain,(
% 3.42/0.83    ( ! [X3] : (~v2_yellow_0(g1_orders_2(X3,k1_yellow_1(X3))) | r2_lattice3(g1_orders_2(X3,k1_yellow_1(X3)),X3,sK1(g1_orders_2(X3,k1_yellow_1(X3))))) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f445,f79])).
% 3.42/0.83  fof(f445,plain,(
% 3.42/0.83    ( ! [X3] : (r2_lattice3(g1_orders_2(X3,k1_yellow_1(X3)),X3,sK1(g1_orders_2(X3,k1_yellow_1(X3)))) | ~l1_orders_2(g1_orders_2(X3,k1_yellow_1(X3))) | ~v2_yellow_0(g1_orders_2(X3,k1_yellow_1(X3)))) )),
% 3.42/0.83    inference(superposition,[],[f55,f374])).
% 3.42/0.83  fof(f55,plain,(
% 3.42/0.83    ( ! [X0] : (r2_lattice3(X0,u1_struct_0(X0),sK1(X0)) | ~l1_orders_2(X0) | ~v2_yellow_0(X0)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f30])).
% 3.42/0.83  fof(f403,plain,(
% 3.42/0.83    ( ! [X2,X0,X3,X1] : (~r2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X3,X0) | ~m1_subset_1(X0,X1) | ~r2_hidden(X2,X3) | r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0) | ~m1_subset_1(X2,X1)) )),
% 3.42/0.83    inference(forward_demodulation,[],[f380,f374])).
% 3.42/0.83  fof(f380,plain,(
% 3.42/0.83    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) | ~r2_hidden(X2,X3) | r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0) | ~r2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X3,X0)) )),
% 3.42/0.83    inference(backward_demodulation,[],[f189,f374])).
% 3.42/0.83  fof(f189,plain,(
% 3.42/0.83    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) | ~r2_hidden(X2,X3) | r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0) | ~r2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X3,X0)) )),
% 3.42/0.83    inference(resolution,[],[f57,f79])).
% 3.42/0.83  fof(f57,plain,(
% 3.42/0.83    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f32])).
% 3.42/0.83  fof(f32,plain,(
% 3.42/0.83    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.42/0.83    inference(flattening,[],[f31])).
% 3.42/0.83  fof(f31,plain,(
% 3.42/0.83    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.42/0.83    inference(ennf_transformation,[],[f8])).
% 3.42/0.83  fof(f8,axiom,(
% 3.42/0.83    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 3.42/0.83  fof(f1131,plain,(
% 3.42/0.83    v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.42/0.83    inference(resolution,[],[f855,f408])).
% 3.42/0.83  fof(f855,plain,(
% 3.42/0.83    ( ! [X0] : (~r2_hidden(X0,sK0) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),X0)) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f854,f408])).
% 3.42/0.83  fof(f854,plain,(
% 3.42/0.83    ( ! [X0] : (k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),X0)) )),
% 3.42/0.83    inference(duplicate_literal_removal,[],[f847])).
% 3.42/0.83  fof(f847,plain,(
% 3.42/0.83    ( ! [X0] : (k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK4(sK0,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),X0) | k3_tarski(sK0) = sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.42/0.83    inference(resolution,[],[f846,f68])).
% 3.42/0.83  fof(f68,plain,(
% 3.42/0.83    ( ! [X0,X3,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3) | k3_tarski(X0) = X1) )),
% 3.42/0.83    inference(cnf_transformation,[],[f2])).
% 3.42/0.83  fof(f846,plain,(
% 3.42/0.83    ( ! [X0] : (r2_hidden(sK4(sK0,X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k3_tarski(sK0) = X0 | ~r2_hidden(X0,sK0) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.42/0.83    inference(subsumption_resolution,[],[f845,f68])).
% 3.42/0.83  fof(f845,plain,(
% 3.42/0.83    ( ! [X0] : (v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k3_tarski(sK0) = X0 | ~r2_hidden(X0,sK0) | r2_hidden(sK4(sK0,X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r2_hidden(sK4(sK0,X0),X0)) )),
% 3.42/0.83    inference(duplicate_literal_removal,[],[f838])).
% 3.42/0.83  fof(f838,plain,(
% 3.42/0.83    ( ! [X0] : (v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k3_tarski(sK0) = X0 | ~r2_hidden(X0,sK0) | k3_tarski(sK0) = X0 | r2_hidden(sK4(sK0,X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r2_hidden(sK4(sK0,X0),X0)) )),
% 3.42/0.83    inference(resolution,[],[f790,f133])).
% 3.42/0.83  fof(f133,plain,(
% 3.42/0.83    ( ! [X4,X5,X3] : (~r1_tarski(sK6(X3,X4),X5) | k3_tarski(X3) = X4 | r2_hidden(sK4(X3,X4),X5) | r2_hidden(sK4(X3,X4),X4)) )),
% 3.42/0.83    inference(resolution,[],[f69,f65])).
% 3.42/0.83  fof(f790,plain,(
% 3.42/0.83    ( ! [X2] : (r1_tarski(sK6(sK0,X2),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k3_tarski(sK0) = X2 | ~r2_hidden(X2,sK0)) )),
% 3.42/0.83    inference(resolution,[],[f784,f170])).
% 3.42/0.83  fof(f170,plain,(
% 3.42/0.83    ( ! [X0,X1] : (r2_hidden(sK6(X1,X0),X1) | k3_tarski(X1) = X0 | ~r2_hidden(X0,X1)) )),
% 3.42/0.83    inference(duplicate_literal_removal,[],[f166])).
% 3.42/0.83  fof(f166,plain,(
% 3.42/0.83    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k3_tarski(X1) = X0 | r2_hidden(sK6(X1,X0),X1) | r2_hidden(sK6(X1,X0),X1) | k3_tarski(X1) = X0) )),
% 3.42/0.83    inference(resolution,[],[f161,f70])).
% 3.42/0.83  fof(f161,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X1,X2),X0) | ~r2_hidden(X0,X1) | k3_tarski(X1) = X2 | r2_hidden(sK6(X1,X2),X1)) )),
% 3.42/0.83    inference(duplicate_literal_removal,[],[f160])).
% 3.42/0.83  fof(f160,plain,(
% 3.42/0.83    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(sK4(X1,X2),X0) | k3_tarski(X1) = X2 | r2_hidden(sK6(X1,X2),X1) | k3_tarski(X1) = X2) )),
% 3.42/0.83    inference(resolution,[],[f68,f70])).
% 3.42/0.83  fof(f408,plain,(
% 3.42/0.83    r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)),
% 3.42/0.83    inference(forward_demodulation,[],[f407,f374])).
% 3.42/0.83  fof(f407,plain,(
% 3.42/0.83    r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.42/0.83    inference(subsumption_resolution,[],[f386,f40])).
% 3.42/0.83  fof(f386,plain,(
% 3.42/0.83    v1_xboole_0(sK0) | r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.42/0.83    inference(backward_demodulation,[],[f105,f374])).
% 3.42/0.83  fof(f105,plain,(
% 3.42/0.83    r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v1_xboole_0(u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.42/0.83    inference(subsumption_resolution,[],[f104,f79])).
% 3.42/0.83  fof(f104,plain,(
% 3.42/0.83    ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v1_xboole_0(u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.42/0.83    inference(resolution,[],[f92,f76])).
% 3.42/0.83  fof(f92,plain,(
% 3.42/0.83    ( ! [X0] : (~v2_yellow_0(X0) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)) | r2_hidden(sK1(X0),u1_struct_0(X0))) )),
% 3.42/0.83    inference(resolution,[],[f54,f62])).
% 3.42/0.83  fof(f62,plain,(
% 3.42/0.83    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 3.42/0.83    inference(cnf_transformation,[],[f35])).
% 3.42/0.83  fof(f35,plain,(
% 3.42/0.83    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.42/0.83    inference(flattening,[],[f34])).
% 3.42/0.83  fof(f34,plain,(
% 3.42/0.83    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.42/0.83    inference(ennf_transformation,[],[f4])).
% 3.42/0.83  fof(f4,axiom,(
% 3.42/0.83    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.42/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 3.42/0.83  % SZS output end Proof for theBenchmark
% 3.42/0.83  % (5818)------------------------------
% 3.42/0.83  % (5818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.83  % (5818)Termination reason: Refutation
% 3.42/0.83  
% 3.42/0.83  % (5818)Memory used [KB]: 8443
% 3.42/0.83  % (5818)Time elapsed: 0.375 s
% 3.42/0.83  % (5818)------------------------------
% 3.42/0.83  % (5818)------------------------------
% 3.42/0.83  % (5810)Success in time 0.469 s
%------------------------------------------------------------------------------
