%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1474+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 25.34s
% Output     : Refutation 26.16s
% Verified   : 
% Statistics : Number of formulae       :  186 (2913 expanded)
%              Number of leaves         :   16 ( 509 expanded)
%              Depth                    :   38
%              Number of atoms          :  659 (14763 expanded)
%              Number of equality atoms :   63 ( 633 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66906,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66905,f65996])).

fof(f65996,plain,(
    r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0)) ),
    inference(forward_demodulation,[],[f65995,f28802])).

fof(f28802,plain,(
    k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f28742,f12067])).

fof(f12067,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f11990,f7646])).

fof(f7646,plain,(
    ~ v1_xboole_0(sK236(sK0)) ),
    inference(subsumption_resolution,[],[f7645,f3930])).

fof(f3930,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2858])).

fof(f2858,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2857])).

fof(f2857,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2828])).

fof(f2828,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2827])).

fof(f2827,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

fof(f7645,plain,
    ( ~ v10_lattices(sK0)
    | ~ v1_xboole_0(sK236(sK0)) ),
    inference(subsumption_resolution,[],[f7453,f3929])).

fof(f3929,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2858])).

fof(f7453,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v1_xboole_0(sK236(sK0)) ),
    inference(resolution,[],[f3931,f5158])).

fof(f5158,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v1_xboole_0(sK236(X0)) ) ),
    inference(cnf_transformation,[],[f3552])).

fof(f3552,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3551])).

fof(f3551,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2053])).

fof(f2053,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc14_lattices)).

fof(f3931,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2858])).

fof(f11990,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK236(sK0)) ),
    inference(resolution,[],[f7644,f4091])).

fof(f4091,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f2964])).

fof(f2964,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f541])).

fof(f541,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f7644,plain,(
    m1_subset_1(sK236(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f7643,f3930])).

fof(f7643,plain,
    ( ~ v10_lattices(sK0)
    | m1_subset_1(sK236(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f7452,f3929])).

fof(f7452,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | m1_subset_1(sK236(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3931,f5157])).

fof(f5157,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(sK236(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f3552])).

fof(f28742,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f28739])).

fof(f28739,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2) ),
    inference(resolution,[],[f8182,f3928])).

fof(f3928,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2858])).

fof(f8182,plain,(
    ! [X138,X137] :
      ( ~ m1_subset_1(X138,X137)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X137)
      | k4_tarski(X138,sK2) = k1_domain_1(X137,u1_struct_0(sK0),X138,sK2) ) ),
    inference(resolution,[],[f3927,f5221])).

fof(f5221,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X1)
      | k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f3604])).

fof(f3604,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3603])).

fof(f3603,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1934])).

fof(f1934,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

fof(f3927,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2858])).

fof(f65995,plain,(
    r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f65994,f3927])).

fof(f65994,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f65993,f3928])).

fof(f65993,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f65992,f3931])).

fof(f65992,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f65991,f3930])).

fof(f65991,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f65970,f3929])).

fof(f65970,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(resolution,[],[f65960,f4024])).

fof(f4024,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_lattices(X0,X1,X2)
      | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) ) ),
    inference(cnf_transformation,[],[f2902])).

fof(f2902,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2901])).

fof(f2901,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2746])).

fof(f2746,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_filter_1)).

fof(f65960,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f65954,f28804])).

fof(f28804,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | r3_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f25101,f28802])).

fof(f25101,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | r3_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f15379,f15377])).

fof(f15377,plain,
    ( r3_orders_2(k3_lattice3(sK0),sK1,sK2)
    | r3_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f15363,f15239])).

fof(f15239,plain,(
    sK1 = k4_lattice3(sK0,sK1) ),
    inference(resolution,[],[f7558,f3928])).

fof(f7558,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattice3(sK0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f7557,f3930])).

fof(f7557,plain,(
    ! [X1] :
      ( ~ v10_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattice3(sK0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f7129,f3929])).

fof(f7129,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattice3(sK0,X1) = X1 ) ),
    inference(resolution,[],[f3931,f3962])).

fof(f3962,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattice3(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f2874])).

fof(f2874,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2873])).

fof(f2873,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2808])).

fof(f2808,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

fof(f15363,plain,
    ( r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),sK2)
    | r3_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f3925,f15238])).

fof(f15238,plain,(
    sK2 = k4_lattice3(sK0,sK2) ),
    inference(resolution,[],[f7558,f3927])).

fof(f3925,plain,
    ( r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2))
    | r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f2858])).

fof(f15379,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),sK1,sK2)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(backward_demodulation,[],[f15370,f15239])).

fof(f15370,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),sK2)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(backward_demodulation,[],[f8954,f15238])).

fof(f8954,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f8953,f3927])).

fof(f8953,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f8952,f3928])).

fof(f8952,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f8951,f3931])).

fof(f8951,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f8950,f3930])).

fof(f8950,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(subsumption_resolution,[],[f8947,f3929])).

fof(f8947,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(resolution,[],[f3926,f4025])).

fof(f4025,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_lattices(X0,X1,X2)
      | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) ) ),
    inference(cnf_transformation,[],[f2902])).

fof(f3926,plain,
    ( ~ r3_lattices(sK0,sK1,sK2)
    | ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f2858])).

fof(f65954,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | r3_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f30953,f65952])).

fof(f65952,plain,(
    k8_filter_1(sK0) = u1_orders_2(k3_lattice3(sK0)) ),
    inference(trivial_inequality_removal,[],[f65951])).

fof(f65951,plain,
    ( k3_lattice3(sK0) != k3_lattice3(sK0)
    | k8_filter_1(sK0) = u1_orders_2(k3_lattice3(sK0)) ),
    inference(superposition,[],[f16724,f62050])).

fof(f62050,plain,(
    k3_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_lattice3(sK0))) ),
    inference(backward_demodulation,[],[f7671,f62048])).

fof(f62048,plain,(
    u1_struct_0(sK0) = u1_struct_0(k3_lattice3(sK0)) ),
    inference(trivial_inequality_removal,[],[f62047])).

fof(f62047,plain,
    ( k3_lattice3(sK0) != k3_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k3_lattice3(sK0)) ),
    inference(superposition,[],[f16723,f7671])).

fof(f16723,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k3_lattice3(sK0)
      | u1_struct_0(sK0) = X0 ) ),
    inference(forward_demodulation,[],[f16520,f7610])).

fof(f7610,plain,(
    k3_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k8_filter_1(sK0)) ),
    inference(backward_demodulation,[],[f7574,f7604])).

fof(f7604,plain,(
    k2_lattice3(sK0) = k8_filter_1(sK0) ),
    inference(subsumption_resolution,[],[f7603,f3930])).

fof(f7603,plain,
    ( ~ v10_lattices(sK0)
    | k2_lattice3(sK0) = k8_filter_1(sK0) ),
    inference(subsumption_resolution,[],[f7266,f3929])).

fof(f7266,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k2_lattice3(sK0) = k8_filter_1(sK0) ),
    inference(resolution,[],[f3931,f4906])).

fof(f4906,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | k8_filter_1(X0) = k2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3387])).

fof(f3387,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = k2_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3386])).

fof(f3386,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = k2_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2818])).

fof(f2818,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = k2_lattice3(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_lattice3)).

fof(f7574,plain,(
    k3_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k2_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7573,f3930])).

fof(f7573,plain,
    ( ~ v10_lattices(sK0)
    | k3_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k2_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7142,f3929])).

fof(f7142,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k3_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k2_lattice3(sK0)) ),
    inference(resolution,[],[f3931,f3974])).

fof(f3974,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f2882])).

fof(f2882,plain,(
    ! [X0] :
      ( k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2881])).

fof(f2881,plain,(
    ! [X0] :
      ( k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2807])).

fof(f2807,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_lattice3)).

fof(f16520,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),k8_filter_1(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f7605,f4899])).

fof(f4899,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f3383])).

fof(f3383,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f1926,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f7605,plain,(
    m1_subset_1(k8_filter_1(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f7602,f7604])).

fof(f7602,plain,(
    m1_subset_1(k2_lattice3(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f7601,f3930])).

fof(f7601,plain,
    ( ~ v10_lattices(sK0)
    | m1_subset_1(k2_lattice3(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f7265,f3929])).

fof(f7265,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | m1_subset_1(k2_lattice3(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f3931,f4905])).

fof(f4905,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f3385])).

fof(f3385,plain,(
    ! [X0] :
      ( ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3384])).

fof(f3384,plain,(
    ! [X0] :
      ( ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2810])).

fof(f2810,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattice3)).

fof(f7671,plain,(
    k3_lattice3(sK0) = g1_orders_2(u1_struct_0(k3_lattice3(sK0)),u1_orders_2(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f7670,f7570])).

fof(f7570,plain,(
    l1_orders_2(k3_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7569,f3930])).

fof(f7569,plain,
    ( ~ v10_lattices(sK0)
    | l1_orders_2(k3_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7136,f3929])).

fof(f7136,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | l1_orders_2(k3_lattice3(sK0)) ),
    inference(resolution,[],[f3931,f3968])).

fof(f3968,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | l1_orders_2(k3_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f2878])).

fof(f2878,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2877])).

fof(f2877,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2811])).

fof(f2811,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattice3)).

fof(f7670,plain,
    ( ~ l1_orders_2(k3_lattice3(sK0))
    | k3_lattice3(sK0) = g1_orders_2(u1_struct_0(k3_lattice3(sK0)),u1_orders_2(k3_lattice3(sK0))) ),
    inference(resolution,[],[f7562,f4898])).

fof(f4898,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f3382])).

fof(f3382,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3381])).

fof(f3381,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1859])).

fof(f1859,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f7562,plain,(
    v1_orders_2(k3_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7561,f3930])).

fof(f7561,plain,
    ( ~ v10_lattices(sK0)
    | v1_orders_2(k3_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7132,f3929])).

fof(f7132,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v1_orders_2(k3_lattice3(sK0)) ),
    inference(resolution,[],[f3931,f3964])).

fof(f3964,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_orders_2(k3_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f2878])).

fof(f16724,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k3_lattice3(sK0)
      | k8_filter_1(sK0) = X3 ) ),
    inference(forward_demodulation,[],[f16521,f7610])).

fof(f16521,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),k8_filter_1(sK0))
      | k8_filter_1(sK0) = X3 ) ),
    inference(resolution,[],[f7605,f4900])).

fof(f4900,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f3383])).

fof(f30953,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f30952,f7570])).

fof(f30952,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ l1_orders_2(k3_lattice3(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f30951,f28204])).

fof(f28204,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f28202,f3927])).

fof(f28202,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f7556,f15238])).

fof(f7556,plain,(
    ! [X0] :
      ( m1_subset_1(k4_lattice3(sK0,X0),u1_struct_0(k3_lattice3(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7555,f3930])).

fof(f7555,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k4_lattice3(sK0,X0),u1_struct_0(k3_lattice3(sK0))) ) ),
    inference(subsumption_resolution,[],[f7128,f3929])).

fof(f7128,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k4_lattice3(sK0,X0),u1_struct_0(k3_lattice3(sK0))) ) ),
    inference(resolution,[],[f3931,f3961])).

fof(f3961,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) ) ),
    inference(cnf_transformation,[],[f2872])).

fof(f2872,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2871])).

fof(f2871,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2812])).

fof(f2812,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattice3)).

fof(f30951,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | r3_lattices(sK0,sK1,sK2)
    | ~ l1_orders_2(k3_lattice3(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f30906,f28505])).

fof(f28505,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f28503,f3928])).

fof(f28503,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[],[f7556,f15239])).

fof(f30906,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | r3_lattices(sK0,sK1,sK2)
    | ~ l1_orders_2(k3_lattice3(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(duplicate_literal_removal,[],[f30905])).

fof(f30905,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | r3_lattices(sK0,sK1,sK2)
    | ~ l1_orders_2(k3_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(resolution,[],[f15390,f4155])).

fof(f4155,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2991])).

fof(f2991,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1885])).

fof(f1885,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f15390,plain,
    ( r1_orders_2(k3_lattice3(sK0),sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | r3_lattices(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f15385,f15239])).

fof(f15385,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | r1_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | r3_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f15376,f15239])).

fof(f15376,plain,
    ( r1_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | r3_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(k4_lattice3(sK0,sK1),u1_struct_0(k3_lattice3(sK0))) ),
    inference(forward_demodulation,[],[f15369,f15238])).

fof(f15369,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | r3_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(k4_lattice3(sK0,sK1),u1_struct_0(k3_lattice3(sK0)))
    | r1_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2)) ),
    inference(backward_demodulation,[],[f8865,f15238])).

fof(f8865,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(k4_lattice3(sK0,sK1),u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(k4_lattice3(sK0,sK2),u1_struct_0(k3_lattice3(sK0)))
    | r1_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f8864,f7570])).

fof(f8864,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ l1_orders_2(k3_lattice3(sK0))
    | ~ m1_subset_1(k4_lattice3(sK0,sK1),u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(k4_lattice3(sK0,sK2),u1_struct_0(k3_lattice3(sK0)))
    | r1_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f8863,f7564])).

fof(f7564,plain,(
    v3_orders_2(k3_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7563,f3930])).

fof(f7563,plain,
    ( ~ v10_lattices(sK0)
    | v3_orders_2(k3_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7133,f3929])).

fof(f7133,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v3_orders_2(k3_lattice3(sK0)) ),
    inference(resolution,[],[f3931,f3965])).

fof(f3965,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v3_orders_2(k3_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f2878])).

fof(f8863,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ v3_orders_2(k3_lattice3(sK0))
    | ~ l1_orders_2(k3_lattice3(sK0))
    | ~ m1_subset_1(k4_lattice3(sK0,sK1),u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(k4_lattice3(sK0,sK2),u1_struct_0(k3_lattice3(sK0)))
    | r1_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f8848,f7572])).

fof(f7572,plain,(
    ~ v2_struct_0(k3_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7571,f3930])).

fof(f7571,plain,
    ( ~ v10_lattices(sK0)
    | ~ v2_struct_0(k3_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f7137,f3929])).

fof(f7137,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v2_struct_0(k3_lattice3(sK0)) ),
    inference(resolution,[],[f3931,f3969])).

fof(f3969,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v2_struct_0(k3_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f2880])).

fof(f2880,plain,(
    ! [X0] :
      ( ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2879])).

fof(f2879,plain,(
    ! [X0] :
      ( ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2816])).

fof(f2816,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_lattice3)).

fof(f8848,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | v2_struct_0(k3_lattice3(sK0))
    | ~ v3_orders_2(k3_lattice3(sK0))
    | ~ l1_orders_2(k3_lattice3(sK0))
    | ~ m1_subset_1(k4_lattice3(sK0,sK1),u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(k4_lattice3(sK0,sK2),u1_struct_0(k3_lattice3(sK0)))
    | r1_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),k4_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f3925,f3933])).

fof(f3933,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2860])).

fof(f2860,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2859])).

fof(f2859,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1937])).

fof(f1937,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f66905,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0)) ),
    inference(forward_demodulation,[],[f66904,f65952])).

fof(f66904,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f66903,f3927])).

fof(f66903,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(forward_demodulation,[],[f66902,f62048])).

fof(f66902,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f66901,f3928])).

fof(f66901,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(forward_demodulation,[],[f66900,f62048])).

fof(f66900,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f66894,f7570])).

fof(f66894,plain,
    ( ~ l1_orders_2(k3_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k3_lattice3(sK0))) ),
    inference(resolution,[],[f66150,f4154])).

fof(f4154,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2991])).

fof(f66150,plain,(
    ~ r1_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f66149,f3927])).

fof(f66149,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(forward_demodulation,[],[f66148,f62048])).

fof(f66148,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r1_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f66147,f3928])).

fof(f66147,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r1_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(forward_demodulation,[],[f66146,f62048])).

fof(f66146,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r1_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f66145,f7570])).

fof(f66145,plain,
    ( ~ l1_orders_2(k3_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r1_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f66144,f7564])).

fof(f66144,plain,
    ( ~ v3_orders_2(k3_lattice3(sK0))
    | ~ l1_orders_2(k3_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r1_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f66143,f7572])).

fof(f66143,plain,
    ( v2_struct_0(k3_lattice3(sK0))
    | ~ v3_orders_2(k3_lattice3(sK0))
    | ~ l1_orders_2(k3_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK0)))
    | ~ r1_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(resolution,[],[f65961,f3932])).

fof(f3932,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2860])).

fof(f65961,plain,(
    ~ r3_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(resolution,[],[f65960,f15378])).

fof(f15378,plain,
    ( ~ r3_lattices(sK0,sK1,sK2)
    | ~ r3_orders_2(k3_lattice3(sK0),sK1,sK2) ),
    inference(backward_demodulation,[],[f15364,f15239])).

fof(f15364,plain,
    ( ~ r3_orders_2(k3_lattice3(sK0),k4_lattice3(sK0,sK1),sK2)
    | ~ r3_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f3926,f15238])).
%------------------------------------------------------------------------------
