%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:32 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  130 (2354 expanded)
%              Number of leaves         :   11 ( 413 expanded)
%              Depth                    :   25
%              Number of atoms          :  481 (13560 expanded)
%              Number of equality atoms :  108 (1721 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f851,plain,(
    $false ),
    inference(subsumption_resolution,[],[f850,f779])).

fof(f779,plain,(
    ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f775,f740])).

fof(f740,plain,(
    ~ v1_tsep_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f718])).

fof(f718,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f96,f709])).

fof(f709,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f267,f707])).

fof(f707,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f706,f694])).

fof(f694,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f279,f267])).

fof(f279,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_pre_topc(sK0) = X3 ) ),
    inference(resolution,[],[f98,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f98,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f60,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f706,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f705,f271])).

fof(f271,plain,(
    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f270,f149])).

fof(f149,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f148,f136])).

fof(f136,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f109,f60])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f57,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f57,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f148,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f147,f124])).

fof(f124,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f123,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f123,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f122,f60])).

fof(f122,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f103,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f147,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f146,f121])).

fof(f121,plain,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f120,f58])).

fof(f120,plain,
    ( v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f119,f60])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f102,f59])).

fof(f102,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f57,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f146,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f145,f118])).

fof(f118,plain,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f117,f58])).

fof(f117,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f116,f60])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f101,f59])).

fof(f101,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f57,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f145,plain,
    ( ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f144,f58])).

fof(f144,plain,
    ( v2_struct_0(sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f143,f60])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f115,f59])).

fof(f115,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f57,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f270,plain,(
    k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f269,f58])).

fof(f269,plain,
    ( v2_struct_0(sK0)
    | k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f268,f60])).

fof(f268,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f251,f59])).

fof(f251,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f136,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f705,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f704,f58])).

fof(f704,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f703,f136])).

fof(f703,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f702,f60])).

fof(f702,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f700,f59])).

fof(f700,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f326,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f326,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f325,f60])).

fof(f325,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f324,f136])).

fof(f324,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f153,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f153,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f152,f60])).

fof(f152,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f151,f136])).

fof(f151,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f150,f57])).

fof(f150,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f54,plain,
    ( v1_tsep_1(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f267,plain,(
    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f204,f265])).

fof(f265,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f264,f149])).

fof(f264,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f263,f58])).

fof(f263,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f262,f60])).

fof(f262,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f250,f59])).

fof(f250,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f136,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f204,plain,(
    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f203,f124])).

fof(f203,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f118,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f96,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f53,f57])).

fof(f53,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f775,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f139,f773])).

fof(f773,plain,(
    u1_struct_0(sK1) = sK3(sK0,sK1) ),
    inference(resolution,[],[f740,f138])).

fof(f138,plain,
    ( v1_tsep_1(sK1,sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1) ),
    inference(subsumption_resolution,[],[f111,f60])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(resolution,[],[f57,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f139,plain,
    ( ~ v3_pre_topc(sK3(sK0,sK1),sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f112,f60])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK3(sK0,sK1),sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f850,plain,(
    v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f849,f60])).

fof(f849,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f848,f136])).

fof(f848,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(resolution,[],[f717,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f717,plain,(
    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(trivial_inequality_removal,[],[f711])).

fof(f711,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f273,f707])).

fof(f273,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f257,f271])).

fof(f257,plain,
    ( u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f256,f58])).

fof(f256,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f255,f60])).

fof(f255,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f248,f59])).

fof(f248,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f136,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (13589)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (13599)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (13583)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (13585)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (13602)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (13594)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (13586)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (13601)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (13593)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (13581)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (13584)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (13591)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (13588)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.24/0.53  % (13592)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.24/0.53  % (13582)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.24/0.53  % (13597)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.24/0.54  % (13600)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.24/0.54  % (13598)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.24/0.54  % (13579)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.24/0.54  % (13590)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.24/0.54  % (13580)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.54  % (13603)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.42/0.55  % (13595)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.42/0.55  % (13584)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f851,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(subsumption_resolution,[],[f850,f779])).
% 1.42/0.55  fof(f779,plain,(
% 1.42/0.55    ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f775,f740])).
% 1.42/0.55  fof(f740,plain,(
% 1.42/0.55    ~v1_tsep_1(sK1,sK0)),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f718])).
% 1.42/0.55  fof(f718,plain,(
% 1.42/0.55    k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0)),
% 1.42/0.55    inference(backward_demodulation,[],[f96,f709])).
% 1.42/0.55  fof(f709,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 1.42/0.55    inference(backward_demodulation,[],[f267,f707])).
% 1.42/0.55  fof(f707,plain,(
% 1.42/0.55    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f706,f694])).
% 1.42/0.55  fof(f694,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(superposition,[],[f279,f267])).
% 1.42/0.55  fof(f279,plain,(
% 1.42/0.55    ( ! [X2,X3] : (g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = X3) )),
% 1.42/0.55    inference(resolution,[],[f98,f62])).
% 1.42/0.55  fof(f62,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 1.42/0.55    inference(cnf_transformation,[],[f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.55    inference(ennf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.42/0.55  fof(f98,plain,(
% 1.42/0.55    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.42/0.55    inference(resolution,[],[f60,f76])).
% 1.42/0.55  fof(f76,plain,(
% 1.42/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f36])).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.42/0.55  fof(f60,plain,(
% 1.42/0.55    l1_pre_topc(sK0)),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f22])).
% 1.42/0.55  fof(f22,negated_conjecture,(
% 1.42/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 1.42/0.55    inference(negated_conjecture,[],[f21])).
% 1.42/0.55  fof(f21,conjecture,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).
% 1.42/0.55  fof(f706,plain,(
% 1.42/0.55    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 1.42/0.55    inference(forward_demodulation,[],[f705,f271])).
% 1.42/0.55  fof(f271,plain,(
% 1.42/0.55    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(forward_demodulation,[],[f270,f149])).
% 1.42/0.55  fof(f149,plain,(
% 1.42/0.55    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f148,f136])).
% 1.42/0.55  fof(f136,plain,(
% 1.42/0.55    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f109,f60])).
% 1.42/0.55  fof(f109,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.42/0.55    inference(resolution,[],[f57,f77])).
% 1.42/0.55  fof(f77,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f37])).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f17])).
% 1.42/0.55  fof(f17,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.42/0.55  fof(f57,plain,(
% 1.42/0.55    m1_pre_topc(sK1,sK0)),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f148,plain,(
% 1.42/0.55    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f147,f124])).
% 1.42/0.55  fof(f124,plain,(
% 1.42/0.55    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f123,f58])).
% 1.42/0.55  fof(f58,plain,(
% 1.42/0.55    ~v2_struct_0(sK0)),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f123,plain,(
% 1.42/0.55    v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f122,f60])).
% 1.42/0.55  fof(f122,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f103,f59])).
% 1.42/0.55  fof(f59,plain,(
% 1.42/0.55    v2_pre_topc(sK0)),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f103,plain,(
% 1.42/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(resolution,[],[f57,f66])).
% 1.42/0.55  fof(f66,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f29])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,axiom,(
% 1.42/0.55    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 1.42/0.55  fof(f147,plain,(
% 1.42/0.55    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f146,f121])).
% 1.42/0.55  fof(f121,plain,(
% 1.42/0.55    v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f120,f58])).
% 1.42/0.55  fof(f120,plain,(
% 1.42/0.55    v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f119,f60])).
% 1.42/0.55  fof(f119,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f102,f59])).
% 1.42/0.55  fof(f102,plain,(
% 1.42/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(resolution,[],[f57,f65])).
% 1.42/0.55  fof(f65,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_pre_topc(k8_tmap_1(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f29])).
% 1.42/0.55  fof(f146,plain,(
% 1.42/0.55    ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f145,f118])).
% 1.42/0.55  fof(f118,plain,(
% 1.42/0.55    v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f117,f58])).
% 1.42/0.55  fof(f117,plain,(
% 1.42/0.55    v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f116,f60])).
% 1.42/0.55  fof(f116,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f101,f59])).
% 1.42/0.55  fof(f101,plain,(
% 1.42/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(resolution,[],[f57,f64])).
% 1.42/0.55  fof(f64,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f29])).
% 1.42/0.55  fof(f145,plain,(
% 1.42/0.55    ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f144,f58])).
% 1.42/0.55  fof(f144,plain,(
% 1.42/0.55    v2_struct_0(sK0) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f143,f60])).
% 1.42/0.55  fof(f143,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f115,f59])).
% 1.42/0.55  fof(f115,plain,(
% 1.42/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(resolution,[],[f57,f94])).
% 1.42/0.55  fof(f94,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 1.42/0.55    inference(equality_resolution,[],[f93])).
% 1.42/0.55  fof(f93,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k6_tmap_1(X0,u1_struct_0(X1)) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 1.42/0.55    inference(equality_resolution,[],[f67])).
% 1.42/0.55  fof(f67,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X3 | k6_tmap_1(X0,X3) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 1.42/0.55    inference(cnf_transformation,[],[f31])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f30])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).
% 1.42/0.55  fof(f270,plain,(
% 1.42/0.55    k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f269,f58])).
% 1.42/0.55  fof(f269,plain,(
% 1.42/0.55    v2_struct_0(sK0) | k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f268,f60])).
% 1.42/0.55  fof(f268,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f251,f59])).
% 1.42/0.55  fof(f251,plain,(
% 1.42/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.42/0.55    inference(resolution,[],[f136,f86])).
% 1.42/0.55  fof(f86,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f44])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f15])).
% 1.42/0.55  fof(f15,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.42/0.55  fof(f705,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f704,f58])).
% 1.42/0.55  fof(f704,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f703,f136])).
% 1.42/0.55  fof(f703,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f702,f60])).
% 1.42/0.55  fof(f702,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f700,f59])).
% 1.42/0.55  fof(f700,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.42/0.55    inference(resolution,[],[f326,f91])).
% 1.42/0.55  fof(f91,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | v2_struct_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f50])).
% 1.42/0.55  fof(f50,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f49])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f14])).
% 1.42/0.55  fof(f14,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 1.42/0.55  fof(f326,plain,(
% 1.42/0.55    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f325,f60])).
% 1.42/0.55  fof(f325,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f324,f136])).
% 1.42/0.55  fof(f324,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 1.42/0.55    inference(resolution,[],[f153,f89])).
% 1.42/0.55  fof(f89,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f48])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.42/0.55  fof(f153,plain,(
% 1.42/0.55    v3_pre_topc(u1_struct_0(sK1),sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f152,f60])).
% 1.42/0.55  fof(f152,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f151,f136])).
% 1.42/0.55  fof(f151,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f150,f57])).
% 1.42/0.55  fof(f150,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.42/0.55    inference(resolution,[],[f54,f95])).
% 1.42/0.55  fof(f95,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f78])).
% 1.42/0.55  fof(f78,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f39])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f38])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).
% 1.42/0.55  fof(f54,plain,(
% 1.42/0.55    v1_tsep_1(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f267,plain,(
% 1.42/0.55    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 1.42/0.55    inference(backward_demodulation,[],[f204,f265])).
% 1.42/0.55  fof(f265,plain,(
% 1.42/0.55    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 1.42/0.55    inference(forward_demodulation,[],[f264,f149])).
% 1.42/0.55  fof(f264,plain,(
% 1.42/0.55    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f263,f58])).
% 1.42/0.55  fof(f263,plain,(
% 1.42/0.55    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f262,f60])).
% 1.42/0.55  fof(f262,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f250,f59])).
% 1.42/0.55  fof(f250,plain,(
% 1.42/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.42/0.55    inference(resolution,[],[f136,f85])).
% 1.42/0.55  fof(f85,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f204,plain,(
% 1.42/0.55    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f203,f124])).
% 1.42/0.55  fof(f203,plain,(
% 1.42/0.55    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 1.42/0.55    inference(resolution,[],[f118,f63])).
% 1.42/0.55  fof(f63,plain,(
% 1.42/0.55    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f26])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.42/0.55  fof(f96,plain,(
% 1.42/0.55    ~v1_tsep_1(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f53,f57])).
% 1.42/0.55  fof(f53,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f775,plain,(
% 1.42/0.55    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0)),
% 1.42/0.55    inference(backward_demodulation,[],[f139,f773])).
% 1.42/0.55  fof(f773,plain,(
% 1.42/0.55    u1_struct_0(sK1) = sK3(sK0,sK1)),
% 1.42/0.55    inference(resolution,[],[f740,f138])).
% 1.42/0.55  fof(f138,plain,(
% 1.42/0.55    v1_tsep_1(sK1,sK0) | u1_struct_0(sK1) = sK3(sK0,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f111,f60])).
% 1.42/0.55  fof(f111,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | u1_struct_0(sK1) = sK3(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 1.42/0.55    inference(resolution,[],[f57,f80])).
% 1.42/0.55  fof(f80,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tsep_1(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f39])).
% 1.42/0.55  fof(f139,plain,(
% 1.42/0.55    ~v3_pre_topc(sK3(sK0,sK1),sK0) | v1_tsep_1(sK1,sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f112,f60])).
% 1.42/0.55  fof(f112,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | ~v3_pre_topc(sK3(sK0,sK1),sK0) | v1_tsep_1(sK1,sK0)),
% 1.42/0.55    inference(resolution,[],[f57,f81])).
% 1.42/0.55  fof(f81,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(sK3(X0,X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f39])).
% 1.42/0.55  fof(f850,plain,(
% 1.42/0.55    v3_pre_topc(u1_struct_0(sK1),sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f849,f60])).
% 1.42/0.55  fof(f849,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f848,f136])).
% 1.42/0.55  fof(f848,plain,(
% 1.42/0.55    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 1.42/0.55    inference(resolution,[],[f717,f88])).
% 1.42/0.55  fof(f88,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f48])).
% 1.42/0.55  fof(f717,plain,(
% 1.42/0.55    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f711])).
% 1.42/0.55  fof(f711,plain,(
% 1.42/0.55    u1_pre_topc(sK0) != u1_pre_topc(sK0) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 1.42/0.55    inference(backward_demodulation,[],[f273,f707])).
% 1.42/0.55  fof(f273,plain,(
% 1.42/0.55    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 1.42/0.55    inference(backward_demodulation,[],[f257,f271])).
% 1.42/0.55  fof(f257,plain,(
% 1.42/0.55    u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 1.42/0.55    inference(subsumption_resolution,[],[f256,f58])).
% 1.42/0.55  fof(f256,plain,(
% 1.42/0.55    v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 1.42/0.55    inference(subsumption_resolution,[],[f255,f60])).
% 1.42/0.55  fof(f255,plain,(
% 1.42/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 1.42/0.55    inference(subsumption_resolution,[],[f248,f59])).
% 1.42/0.55  fof(f248,plain,(
% 1.42/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 1.42/0.55    inference(resolution,[],[f136,f90])).
% 1.42/0.55  fof(f90,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f50])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (13584)------------------------------
% 1.42/0.55  % (13584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (13584)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (13584)Memory used [KB]: 6524
% 1.42/0.55  % (13584)Time elapsed: 0.125 s
% 1.42/0.55  % (13584)------------------------------
% 1.42/0.55  % (13584)------------------------------
% 1.42/0.55  % (13596)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.42/0.55  % (13604)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.42/0.56  % (13578)Success in time 0.191 s
%------------------------------------------------------------------------------
