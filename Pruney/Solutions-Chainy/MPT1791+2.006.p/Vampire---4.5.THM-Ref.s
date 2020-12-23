%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  141 (3399 expanded)
%              Number of leaves         :   12 ( 889 expanded)
%              Depth                    :   28
%              Number of atoms          :  437 (20088 expanded)
%              Number of equality atoms :   97 (4638 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f622,plain,(
    $false ),
    inference(subsumption_resolution,[],[f619,f614])).

fof(f614,plain,(
    r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(trivial_inequality_removal,[],[f607])).

fof(f607,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f140,f606])).

fof(f606,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f134,f590])).

fof(f590,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f433,f576])).

fof(f576,plain,(
    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f575,f502])).

fof(f502,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f154,f501])).

fof(f501,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f500,f394])).

fof(f394,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f393,f156])).

fof(f156,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f99,f47])).

fof(f47,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f99,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f393,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f390,f99])).

fof(f390,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f74,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f73,f42])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X1] :
      ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X1] :
      ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f500,plain,(
    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f499,f433])).

fof(f499,plain,(
    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f498,f333])).

fof(f333,plain,(
    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f332,f156])).

fof(f332,plain,(
    l1_pre_topc(k6_tmap_1(sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f329,f99])).

fof(f329,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f86,f48])).

fof(f86,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,(
    ! [X7] :
      ( l1_pre_topc(k6_tmap_1(sK0,X7))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f70,f43])).

fof(f70,plain,(
    ! [X7] :
      ( l1_pre_topc(k6_tmap_1(sK0,X7))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f41,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f498,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f480,f50])).

fof(f50,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f480,plain,(
    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f479,f41])).

fof(f479,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f478,f42])).

fof(f478,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f465,f43])).

fof(f465,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f157,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f157,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f155,f156])).

fof(f155,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f99,f48])).

fof(f154,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f153,f43])).

fof(f153,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f152,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f152,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f45,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f575,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f574,f501])).

fof(f574,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f573,f41])).

fof(f573,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f572,f42])).

fof(f572,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f571,f43])).

fof(f571,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f570,f44])).

fof(f570,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f166,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f166,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f165,f131])).

fof(f131,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f130,f41])).

fof(f130,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f129,f42])).

fof(f129,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f116,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f44,f54])).

fof(f165,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f164,f134])).

fof(f164,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f163,f149])).

fof(f149,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f148,f41])).

fof(f148,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f147,f42])).

fof(f147,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f122,f43])).

fof(f122,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f44,f61])).

fof(f163,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f143,f50])).

fof(f143,plain,(
    v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f142,f41])).

fof(f142,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f141,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f120,f43])).

fof(f120,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f44,f59])).

fof(f433,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f432,f341])).

fof(f341,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f340,f41])).

fof(f340,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f339,f42])).

fof(f339,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f338,f43])).

fof(f338,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f336,f157])).

fof(f336,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f249,f56])).

fof(f249,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f248,f43])).

fof(f248,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f247,f157])).

fof(f247,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f159,f51])).

fof(f159,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(backward_demodulation,[],[f97,f156])).

fof(f97,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f92,f43])).

fof(f92,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f432,plain,(
    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f431,f156])).

fof(f431,plain,(
    k5_tmap_1(sK0,k2_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f428,f99])).

fof(f428,plain,
    ( k5_tmap_1(sK0,k2_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f75,f42])).

fof(f75,plain,(
    ! [X2] :
      ( k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f65,f43])).

fof(f65,plain,(
    ! [X2] :
      ( k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f134,plain,(
    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f133,f41])).

fof(f133,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f42])).

fof(f132,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f43])).

fof(f117,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f44,f55])).

fof(f140,plain,
    ( u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f139,f41])).

fof(f139,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f138,f42])).

fof(f138,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f44,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f619,plain,(
    ~ r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(resolution,[],[f599,f125])).

fof(f125,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f114,f43])).

fof(f114,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f599,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f598])).

fof(f598,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f505,f576])).

fof(f505,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f46,f501])).

fof(f46,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n015.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:53:53 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.47  % (10888)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.48  % (10877)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.49  % (10880)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.49  % (10882)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.49  % (10895)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.49  % (10879)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.49  % (10893)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.49  % (10881)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.49  % (10878)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.49  % (10893)Refutation not found, incomplete strategy% (10893)------------------------------
% 0.19/0.49  % (10893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (10893)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (10893)Memory used [KB]: 1663
% 0.19/0.49  % (10893)Time elapsed: 0.093 s
% 0.19/0.49  % (10893)------------------------------
% 0.19/0.49  % (10893)------------------------------
% 0.19/0.49  % (10883)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.49  % (10887)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.49  % (10888)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f622,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f619,f614])).
% 0.19/0.49  fof(f614,plain,(
% 0.19/0.49    r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f607])).
% 0.19/0.49  fof(f607,plain,(
% 0.19/0.49    u1_pre_topc(sK0) != u1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.19/0.49    inference(backward_demodulation,[],[f140,f606])).
% 0.19/0.49  fof(f606,plain,(
% 0.19/0.49    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.19/0.49    inference(backward_demodulation,[],[f134,f590])).
% 0.19/0.49  fof(f590,plain,(
% 0.19/0.49    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.19/0.49    inference(backward_demodulation,[],[f433,f576])).
% 0.19/0.49  fof(f576,plain,(
% 0.19/0.49    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.19/0.49    inference(subsumption_resolution,[],[f575,f502])).
% 0.19/0.49  fof(f502,plain,(
% 0.19/0.49    r2_hidden(sK1,u1_pre_topc(sK0)) | k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.19/0.49    inference(backward_demodulation,[],[f154,f501])).
% 0.19/0.49  fof(f501,plain,(
% 0.19/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.19/0.49    inference(forward_demodulation,[],[f500,f394])).
% 0.19/0.49  fof(f394,plain,(
% 0.19/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.19/0.49    inference(forward_demodulation,[],[f393,f156])).
% 0.19/0.49  fof(f156,plain,(
% 0.19/0.49    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f99,f47])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.49  fof(f99,plain,(
% 0.19/0.49    l1_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f43,f49])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    l1_pre_topc(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f34])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(nnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,negated_conjecture,(
% 0.19/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.19/0.49    inference(negated_conjecture,[],[f12])).
% 0.19/0.49  fof(f12,conjecture,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.19/0.49  fof(f393,plain,(
% 0.19/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,k2_struct_0(sK0)))),
% 0.19/0.49    inference(subsumption_resolution,[],[f390,f99])).
% 0.19/0.49  fof(f390,plain,(
% 0.19/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,k2_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f74,f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f73,f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    v2_pre_topc(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f38])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    ( ! [X1] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f64,f43])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    ( ! [X1] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.49    inference(resolution,[],[f41,f54])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,axiom,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ~v2_struct_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f38])).
% 0.19/0.49  fof(f500,plain,(
% 0.19/0.49    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(sK0))),
% 0.19/0.49    inference(forward_demodulation,[],[f499,f433])).
% 0.19/0.49  fof(f499,plain,(
% 0.19/0.49    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))))),
% 0.19/0.49    inference(subsumption_resolution,[],[f498,f333])).
% 0.19/0.49  fof(f333,plain,(
% 0.19/0.49    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.19/0.49    inference(forward_demodulation,[],[f332,f156])).
% 0.19/0.49  fof(f332,plain,(
% 0.19/0.49    l1_pre_topc(k6_tmap_1(sK0,k2_struct_0(sK0)))),
% 0.19/0.49    inference(subsumption_resolution,[],[f329,f99])).
% 0.19/0.49  fof(f329,plain,(
% 0.19/0.49    l1_pre_topc(k6_tmap_1(sK0,k2_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f86,f48])).
% 0.19/0.49  fof(f86,plain,(
% 0.19/0.49    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X7))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f85,f42])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    ( ! [X7] : (l1_pre_topc(k6_tmap_1(sK0,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f70,f43])).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    ( ! [X7] : (l1_pre_topc(k6_tmap_1(sK0,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.49    inference(resolution,[],[f41,f61])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.19/0.49  fof(f498,plain,(
% 0.19/0.49    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.19/0.49    inference(resolution,[],[f480,f50])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(flattening,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.19/0.49  fof(f480,plain,(
% 0.19/0.49    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.19/0.49    inference(subsumption_resolution,[],[f479,f41])).
% 0.19/0.49  fof(f479,plain,(
% 0.19/0.49    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f478,f42])).
% 0.19/0.49  fof(f478,plain,(
% 0.19/0.49    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f465,f43])).
% 0.19/0.49  fof(f465,plain,(
% 0.19/0.49    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f157,f59])).
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f157,plain,(
% 0.19/0.49    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.49    inference(backward_demodulation,[],[f155,f156])).
% 0.19/0.49  fof(f155,plain,(
% 0.19/0.49    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.49    inference(resolution,[],[f99,f48])).
% 0.19/0.49  fof(f154,plain,(
% 0.19/0.49    r2_hidden(sK1,u1_pre_topc(sK0)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f153,f43])).
% 0.19/0.49  fof(f153,plain,(
% 0.19/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f152,f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f38])).
% 0.19/0.49  fof(f152,plain,(
% 0.19/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.19/0.49    inference(resolution,[],[f45,f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(nnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    v3_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f38])).
% 0.19/0.49  fof(f575,plain,(
% 0.19/0.49    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) | ~r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.19/0.49    inference(forward_demodulation,[],[f574,f501])).
% 0.19/0.49  fof(f574,plain,(
% 0.19/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.19/0.49    inference(subsumption_resolution,[],[f573,f41])).
% 0.19/0.49  fof(f573,plain,(
% 0.19/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f572,f42])).
% 0.19/0.49  fof(f572,plain,(
% 0.19/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~r2_hidden(sK1,u1_pre_topc(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f571,f43])).
% 0.19/0.49  fof(f571,plain,(
% 0.19/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f570,f44])).
% 0.19/0.49  fof(f570,plain,(
% 0.19/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(superposition,[],[f166,f56])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(nnf_transformation,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.19/0.49  fof(f166,plain,(
% 0.19/0.49    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.19/0.49    inference(forward_demodulation,[],[f165,f131])).
% 0.19/0.49  fof(f131,plain,(
% 0.19/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.19/0.49    inference(subsumption_resolution,[],[f130,f41])).
% 0.19/0.49  fof(f130,plain,(
% 0.19/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f129,f42])).
% 0.19/0.49  fof(f129,plain,(
% 0.19/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f116,f43])).
% 0.19/0.49  fof(f116,plain,(
% 0.19/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f44,f54])).
% 0.19/0.49  fof(f165,plain,(
% 0.19/0.49    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1))),
% 0.19/0.49    inference(forward_demodulation,[],[f164,f134])).
% 0.19/0.49  fof(f164,plain,(
% 0.19/0.49    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.19/0.49    inference(subsumption_resolution,[],[f163,f149])).
% 0.19/0.49  fof(f149,plain,(
% 0.19/0.49    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.19/0.49    inference(subsumption_resolution,[],[f148,f41])).
% 0.19/0.49  fof(f148,plain,(
% 0.19/0.49    l1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f147,f42])).
% 0.19/0.49  fof(f147,plain,(
% 0.19/0.49    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f122,f43])).
% 0.19/0.49  fof(f122,plain,(
% 0.19/0.49    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f44,f61])).
% 0.19/0.49  fof(f163,plain,(
% 0.19/0.49    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.19/0.49    inference(resolution,[],[f143,f50])).
% 0.19/0.49  fof(f143,plain,(
% 0.19/0.49    v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.19/0.49    inference(subsumption_resolution,[],[f142,f41])).
% 0.19/0.49  fof(f142,plain,(
% 0.19/0.49    v1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f141,f42])).
% 0.19/0.49  fof(f141,plain,(
% 0.19/0.49    v1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f120,f43])).
% 0.19/0.49  fof(f120,plain,(
% 0.19/0.49    v1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f44,f59])).
% 0.19/0.49  fof(f433,plain,(
% 0.19/0.49    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.19/0.49    inference(forward_demodulation,[],[f432,f341])).
% 0.19/0.49  fof(f341,plain,(
% 0.19/0.49    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))),
% 0.19/0.49    inference(subsumption_resolution,[],[f340,f41])).
% 0.19/0.49  fof(f340,plain,(
% 0.19/0.49    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f339,f42])).
% 0.19/0.49  fof(f339,plain,(
% 0.19/0.49    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f338,f43])).
% 0.19/0.49  fof(f338,plain,(
% 0.19/0.49    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f336,f157])).
% 0.19/0.49  fof(f336,plain,(
% 0.19/0.49    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f249,f56])).
% 0.19/0.49  fof(f249,plain,(
% 0.19/0.49    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.19/0.49    inference(subsumption_resolution,[],[f248,f43])).
% 0.19/0.49  fof(f248,plain,(
% 0.19/0.49    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f247,f157])).
% 0.19/0.49  fof(f247,plain,(
% 0.19/0.49    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.19/0.49    inference(resolution,[],[f159,f51])).
% 0.19/0.49  fof(f159,plain,(
% 0.19/0.49    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.19/0.49    inference(backward_demodulation,[],[f97,f156])).
% 0.19/0.49  fof(f97,plain,(
% 0.19/0.49    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f92,f43])).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    v3_pre_topc(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.49    inference(resolution,[],[f42,f58])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.49    inference(flattening,[],[f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.19/0.49  fof(f432,plain,(
% 0.19/0.49    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.19/0.49    inference(forward_demodulation,[],[f431,f156])).
% 0.19/0.49  fof(f431,plain,(
% 0.19/0.49    k5_tmap_1(sK0,k2_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,k2_struct_0(sK0)))),
% 0.19/0.49    inference(subsumption_resolution,[],[f428,f99])).
% 0.19/0.49  fof(f428,plain,(
% 0.19/0.49    k5_tmap_1(sK0,k2_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,k2_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f76,f48])).
% 0.19/0.49  fof(f76,plain,(
% 0.19/0.49    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f75,f42])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    ( ! [X2] : (k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f65,f43])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ( ! [X2] : (k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.50    inference(resolution,[],[f41,f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f134,plain,(
% 0.19/0.50    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f133,f41])).
% 0.19/0.50  fof(f133,plain,(
% 0.19/0.50    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f132,f42])).
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f117,f43])).
% 0.19/0.50  fof(f117,plain,(
% 0.19/0.50    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f44,f55])).
% 0.19/0.50  fof(f140,plain,(
% 0.19/0.50    u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f139,f41])).
% 0.19/0.50  fof(f139,plain,(
% 0.19/0.50    r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f138,f42])).
% 0.19/0.50  fof(f138,plain,(
% 0.19/0.50    r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f119,f43])).
% 0.19/0.50  fof(f119,plain,(
% 0.19/0.50    r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f44,f57])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f40])).
% 0.19/0.50  fof(f619,plain,(
% 0.19/0.50    ~r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.19/0.50    inference(resolution,[],[f599,f125])).
% 0.19/0.50  fof(f125,plain,(
% 0.19/0.50    v3_pre_topc(sK1,sK0) | ~r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f114,f43])).
% 0.19/0.50  fof(f114,plain,(
% 0.19/0.50    v3_pre_topc(sK1,sK0) | ~r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.19/0.50    inference(resolution,[],[f44,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f39])).
% 0.19/0.50  fof(f599,plain,(
% 0.19/0.50    ~v3_pre_topc(sK1,sK0)),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f598])).
% 0.19/0.50  fof(f598,plain,(
% 0.19/0.50    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.19/0.50    inference(backward_demodulation,[],[f505,f576])).
% 0.19/0.50  fof(f505,plain,(
% 0.19/0.50    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 0.19/0.50    inference(backward_demodulation,[],[f46,f501])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f38])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (10888)------------------------------
% 0.19/0.50  % (10888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (10888)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (10888)Memory used [KB]: 1791
% 0.19/0.50  % (10888)Time elapsed: 0.100 s
% 0.19/0.50  % (10888)------------------------------
% 0.19/0.50  % (10888)------------------------------
% 0.19/0.50  % (10887)Refutation not found, incomplete strategy% (10887)------------------------------
% 0.19/0.50  % (10887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (10887)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (10887)Memory used [KB]: 10618
% 0.19/0.50  % (10887)Time elapsed: 0.105 s
% 0.19/0.50  % (10887)------------------------------
% 0.19/0.50  % (10887)------------------------------
% 0.19/0.50  % (10889)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.50  % (10900)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.50  % (10885)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.50  % (10885)Refutation not found, incomplete strategy% (10885)------------------------------
% 0.19/0.50  % (10885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (10885)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (10885)Memory used [KB]: 10618
% 0.19/0.50  % (10885)Time elapsed: 0.103 s
% 0.19/0.50  % (10885)------------------------------
% 0.19/0.50  % (10885)------------------------------
% 0.19/0.50  % (10899)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.50  % (10890)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.50  % (10886)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.51  % (10898)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.51  % (10894)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.51  % (10896)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.51  % (10884)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (10884)Refutation not found, incomplete strategy% (10884)------------------------------
% 0.19/0.51  % (10884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (10884)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (10884)Memory used [KB]: 6140
% 0.19/0.51  % (10884)Time elapsed: 0.073 s
% 0.19/0.51  % (10884)------------------------------
% 0.19/0.51  % (10884)------------------------------
% 0.19/0.51  % (10897)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.51  % (10891)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.51  % (10892)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.51  % (10876)Success in time 0.17 s
%------------------------------------------------------------------------------
