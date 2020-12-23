%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1143+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 748 expanded)
%              Number of leaves         :   13 ( 144 expanded)
%              Depth                    :   20
%              Number of atoms          :  234 (2684 expanded)
%              Number of equality atoms :   21 (  92 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(global_subsumption,[],[f106,f107,f196])).

fof(f196,plain,(
    v6_orders_2(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f195,f36])).

fof(f36,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f195,plain,
    ( ~ l1_orders_2(sK0)
    | v6_orders_2(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f194,f107])).

fof(f194,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v6_orders_2(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f187,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(f187,plain,(
    r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f185,f121])).

fof(f121,plain,(
    r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f120,f83])).

fof(f83,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f66,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f66,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f120,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f75,f64])).

fof(f64,plain,(
    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f63,plain,
    ( r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v3_orders_2(X0)
      | r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_relat_2(X0,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(sK1,sK1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f73,f71])).

fof(f71,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f70,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

% (552)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f65,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f73,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1,sK1),X0)
      | ~ r1_relat_2(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(f67,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f33,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f185,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f177,f184])).

fof(f184,plain,(
    sK1 = sK3(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(global_subsumption,[],[f106,f107,f183])).

fof(f183,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k1_tarski(sK1))
    | v6_orders_2(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f151,f107])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(u1_orders_2(sK0),k1_tarski(X0)) = X0
      | v6_orders_2(k1_tarski(X0),sK0) ) ),
    inference(subsumption_resolution,[],[f150,f36])).

fof(f150,plain,(
    ! [X0] :
      ( sK3(u1_orders_2(sK0),k1_tarski(X0)) = X0
      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v6_orders_2(k1_tarski(X0),sK0) ) ),
    inference(resolution,[],[f135,f38])).

fof(f135,plain,(
    ! [X5] :
      ( r7_relat_2(u1_orders_2(sK0),k1_tarski(X5))
      | sK3(u1_orders_2(sK0),k1_tarski(X5)) = X5 ) ),
    inference(resolution,[],[f91,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f91,plain,(
    ! [X2] :
      ( r2_hidden(sK3(u1_orders_2(sK0),X2),X2)
      | r7_relat_2(u1_orders_2(sK0),X2) ) ),
    inference(resolution,[],[f83,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_2)).

fof(f177,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k1_tarski(sK1)),sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f175,f83])).

fof(f175,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k1_tarski(sK1)),sK1),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f49,f166])).

fof(f166,plain,(
    sK1 = sK2(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(global_subsumption,[],[f106,f107,f165])).

fof(f165,plain,
    ( sK1 = sK2(u1_orders_2(sK0),k1_tarski(sK1))
    | v6_orders_2(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f149,f107])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(u1_orders_2(sK0),k1_tarski(X0)) = X0
      | v6_orders_2(k1_tarski(X0),sK0) ) ),
    inference(subsumption_resolution,[],[f148,f36])).

fof(f148,plain,(
    ! [X0] :
      ( sK2(u1_orders_2(sK0),k1_tarski(X0)) = X0
      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v6_orders_2(k1_tarski(X0),sK0) ) ),
    inference(resolution,[],[f126,f38])).

fof(f126,plain,(
    ! [X5] :
      ( r7_relat_2(u1_orders_2(sK0),k1_tarski(X5))
      | sK2(u1_orders_2(sK0),k1_tarski(X5)) = X5 ) ),
    inference(resolution,[],[f90,f60])).

fof(f90,plain,(
    ! [X1] :
      ( r2_hidden(sK2(u1_orders_2(sK0),X1),X1)
      | r7_relat_2(u1_orders_2(sK0),X1) ) ),
    inference(resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f97,f71])).

fof(f97,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f69,f95])).

fof(f95,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f68,f71])).

fof(f68,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f69,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f106,plain,
    ( ~ v6_orders_2(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f96,f95])).

fof(f96,plain,
    ( ~ v6_orders_2(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f32,f95])).

fof(f32,plain,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
