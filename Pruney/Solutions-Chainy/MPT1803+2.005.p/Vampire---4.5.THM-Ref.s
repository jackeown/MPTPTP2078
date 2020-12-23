%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:36 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  170 (6691 expanded)
%              Number of leaves         :   17 (2487 expanded)
%              Depth                    :   36
%              Number of atoms          :  820 (43152 expanded)
%              Number of equality atoms :  103 (1247 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1994,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1993,f280])).

fof(f280,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f279,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tmap_1(X1,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X2)
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X2)
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X2)
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).

fof(f279,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f169,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f169,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f1993,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1992,f562])).

fof(f562,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f494,f558])).

fof(f558,plain,(
    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f557,f50])).

fof(f557,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f556,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f556,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f486,f52])).

fof(f486,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f233,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f233,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f220,f52])).

fof(f220,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f54,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f494,plain,(
    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f493,f50])).

fof(f493,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f492,f51])).

fof(f492,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f481,f52])).

fof(f481,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f233,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f1992,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1991,f560])).

fof(f560,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f528,f558])).

fof(f528,plain,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f498,f506])).

fof(f506,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f505,f267])).

fof(f267,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f266,f50])).

fof(f266,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f265,f51])).

fof(f265,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f264,f52])).

fof(f264,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f263,f254])).

fof(f254,plain,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f253,f50])).

fof(f253,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f252,f51])).

fof(f252,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f227,f52])).

fof(f227,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f54,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f263,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f262,f257])).

fof(f257,plain,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f256,f50])).

fof(f256,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f51])).

fof(f255,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f52])).

fof(f228,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f54,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f262,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f261,f260])).

fof(f260,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f259,f50])).

fof(f259,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f258,f51])).

fof(f258,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f229,f52])).

fof(f229,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f54,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f261,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f230,f233])).

fof(f230,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f54,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK3(X0,X1,X2)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f505,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f504,f50])).

fof(f504,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f503,f51])).

fof(f503,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f484,f52])).

fof(f484,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f233,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f498,plain,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f497,f267])).

fof(f497,plain,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f496,f50])).

fof(f496,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f495,f51])).

fof(f495,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f482,f52])).

fof(f482,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f233,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1991,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1990,f559])).

fof(f559,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f529,f558])).

fof(f529,plain,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f502,f506])).

fof(f502,plain,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f501,f267])).

fof(f501,plain,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) ),
    inference(subsumption_resolution,[],[f500,f50])).

fof(f500,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f499,f51])).

fof(f499,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f483,f52])).

fof(f483,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f233,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1990,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f1989])).

fof(f1989,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(condensation,[],[f1988])).

fof(f1988,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1987])).

fof(f1987,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1488,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f1488,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f1487,f506])).

fof(f1487,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f1486,f267])).

fof(f1486,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f1485,f558])).

fof(f1485,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f1484,f1410])).

fof(f1410,plain,(
    u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1409,f560])).

fof(f1409,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1408,f1060])).

fof(f1060,plain,(
    r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) ),
    inference(resolution,[],[f563,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f563,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),X6) ) ),
    inference(backward_demodulation,[],[f278,f558])).

fof(f278,plain,(
    ! [X6] :
      ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f277,f267])).

fof(f277,plain,(
    ! [X6] :
      ( r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f276,f50])).

fof(f276,plain,(
    ! [X6] :
      ( r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f275,f51])).

fof(f275,plain,(
    ! [X6] :
      ( r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f274,f52])).

fof(f274,plain,(
    ! [X6] :
      ( r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f273,f233])).

fof(f273,plain,(
    ! [X6] :
      ( r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f232,plain,(
    ! [X6] :
      ( r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f84])).

fof(f84,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).

fof(f1408,plain,
    ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)
    | u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1407,f559])).

fof(f1407,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)
    | u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f537,f562])).

fof(f537,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f512,f506])).

fof(f512,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X1) ) ),
    inference(backward_demodulation,[],[f309,f506])).

fof(f309,plain,(
    ! [X1] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f308,f50])).

fof(f308,plain,(
    ! [X1] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f307,f51])).

fof(f307,plain,(
    ! [X1] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f306,f52])).

fof(f306,plain,(
    ! [X1] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f54])).

fof(f288,plain,(
    ! [X1] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f56,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK4(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
                    & u1_struct_0(X1) = sK4(X0,X1,X2)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
        & u1_struct_0(X1) = sK4(X0,X1,X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f56,plain,(
    ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1484,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f1483,f560])).

fof(f1483,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1482,f1060])).

% (7444)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f1482,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))))
    | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1481,f559])).

fof(f1481,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))))
    | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f539,f562])).

fof(f539,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2)))
      | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f538,f506])).

fof(f538,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2)))
      | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f513,f506])).

fof(f513,plain,(
    ! [X2] :
      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2)))
      | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X2) ) ),
    inference(backward_demodulation,[],[f313,f506])).

fof(f313,plain,(
    ! [X2] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2)
      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f312,f50])).

fof(f312,plain,(
    ! [X2] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2)
      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f311,f51])).

fof(f311,plain,(
    ! [X2] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2)
      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f310,f52])).

fof(f310,plain,(
    ! [X2] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2)
      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f289,f54])).

fof(f289,plain,(
    ! [X2] :
      ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2)
      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f56,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:00:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (7431)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (7437)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (7440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (7445)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (7440)Refutation not found, incomplete strategy% (7440)------------------------------
% 0.21/0.48  % (7440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7441)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (7433)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (7434)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (7429)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (7430)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (7428)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (7440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7440)Memory used [KB]: 1791
% 0.21/0.49  % (7440)Time elapsed: 0.066 s
% 0.21/0.49  % (7440)------------------------------
% 0.21/0.49  % (7440)------------------------------
% 0.21/0.49  % (7428)Refutation not found, incomplete strategy% (7428)------------------------------
% 0.21/0.49  % (7428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7428)Memory used [KB]: 10618
% 0.21/0.49  % (7428)Time elapsed: 0.083 s
% 0.21/0.49  % (7428)------------------------------
% 0.21/0.49  % (7428)------------------------------
% 0.21/0.50  % (7427)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (7432)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (7447)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (7447)Refutation not found, incomplete strategy% (7447)------------------------------
% 0.21/0.51  % (7447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7447)Memory used [KB]: 10618
% 0.21/0.51  % (7447)Time elapsed: 0.096 s
% 0.21/0.51  % (7447)------------------------------
% 0.21/0.51  % (7447)------------------------------
% 0.21/0.51  % (7446)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (7443)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (7439)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (7439)Refutation not found, incomplete strategy% (7439)------------------------------
% 0.21/0.51  % (7439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7439)Memory used [KB]: 6140
% 0.21/0.51  % (7439)Time elapsed: 0.099 s
% 0.21/0.51  % (7439)------------------------------
% 0.21/0.51  % (7439)------------------------------
% 0.21/0.52  % (7435)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.25/0.52  % (7431)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f1994,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(subsumption_resolution,[],[f1993,f280])).
% 1.25/0.52  fof(f280,plain,(
% 1.25/0.52    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f279,f50])).
% 1.25/0.52  fof(f50,plain,(
% 1.25/0.52    ~v2_struct_0(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f41])).
% 1.25/0.52  fof(f41,plain,(
% 1.25/0.52    ((~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) & m1_subset_1(sK2,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.25/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f40,f39,f38])).
% 1.25/0.52  fof(f38,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f39,plain,(
% 1.25/0.52    ? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X2) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f40,plain,(
% 1.25/0.52    ? [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X2) & m1_subset_1(X2,u1_struct_0(sK1))) => (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f16,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f15])).
% 1.25/0.52  fof(f15,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f14])).
% 1.25/0.52  fof(f14,negated_conjecture,(
% 1.25/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 1.25/0.52    inference(negated_conjecture,[],[f13])).
% 1.25/0.52  fof(f13,conjecture,(
% 1.25/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).
% 1.25/0.52  fof(f279,plain,(
% 1.25/0.52    ~v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f169,f60])).
% 1.25/0.52  fof(f60,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f21])).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f20])).
% 1.25/0.52  fof(f20,plain,(
% 1.25/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f2])).
% 1.25/0.52  fof(f2,axiom,(
% 1.25/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.25/0.52  fof(f169,plain,(
% 1.25/0.52    l1_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f52,f57])).
% 1.25/0.52  fof(f57,plain,(
% 1.25/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f17])).
% 1.25/0.52  fof(f17,plain,(
% 1.25/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f1])).
% 1.25/0.52  fof(f1,axiom,(
% 1.25/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.25/0.52  fof(f52,plain,(
% 1.25/0.52    l1_pre_topc(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f41])).
% 1.25/0.52  fof(f1993,plain,(
% 1.25/0.52    v1_xboole_0(u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1992,f562])).
% 1.25/0.52  fof(f562,plain,(
% 1.25/0.52    v1_funct_1(k6_partfun1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(backward_demodulation,[],[f494,f558])).
% 1.25/0.52  fof(f558,plain,(
% 1.25/0.52    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f557,f50])).
% 1.25/0.52  fof(f557,plain,(
% 1.25/0.52    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f556,f51])).
% 1.25/0.52  fof(f51,plain,(
% 1.25/0.52    v2_pre_topc(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f41])).
% 1.25/0.52  fof(f556,plain,(
% 1.25/0.52    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f486,f52])).
% 1.25/0.52  fof(f486,plain,(
% 1.25/0.52    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f233,f69])).
% 1.25/0.52  fof(f69,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f27])).
% 1.25/0.52  fof(f27,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f26])).
% 1.25/0.52  fof(f26,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f4])).
% 1.25/0.52  fof(f4,axiom,(
% 1.25/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).
% 1.25/0.52  fof(f233,plain,(
% 1.25/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(subsumption_resolution,[],[f220,f52])).
% 1.25/0.52  fof(f220,plain,(
% 1.25/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.25/0.52    inference(resolution,[],[f54,f59])).
% 1.25/0.52  fof(f59,plain,(
% 1.25/0.52    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f19,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f11])).
% 1.25/0.52  fof(f11,axiom,(
% 1.25/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.25/0.52  fof(f54,plain,(
% 1.25/0.52    m1_pre_topc(sK1,sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f41])).
% 1.25/0.52  fof(f494,plain,(
% 1.25/0.52    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.25/0.52    inference(subsumption_resolution,[],[f493,f50])).
% 1.25/0.52  fof(f493,plain,(
% 1.25/0.52    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f492,f51])).
% 1.25/0.52  fof(f492,plain,(
% 1.25/0.52    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f481,f52])).
% 1.25/0.52  fof(f481,plain,(
% 1.25/0.52    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f233,f76])).
% 1.25/0.52  fof(f76,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f35])).
% 1.25/0.52  fof(f35,plain,(
% 1.25/0.52    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f34])).
% 1.25/0.52  fof(f34,plain,(
% 1.25/0.52    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f7])).
% 1.25/0.52  fof(f7,axiom,(
% 1.25/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.25/0.52  fof(f1992,plain,(
% 1.25/0.52    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1991,f560])).
% 1.25/0.52  fof(f560,plain,(
% 1.25/0.52    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(backward_demodulation,[],[f528,f558])).
% 1.25/0.52  fof(f528,plain,(
% 1.25/0.52    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(backward_demodulation,[],[f498,f506])).
% 1.25/0.52  fof(f506,plain,(
% 1.25/0.52    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 1.25/0.52    inference(forward_demodulation,[],[f505,f267])).
% 1.25/0.52  fof(f267,plain,(
% 1.25/0.52    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f266,f50])).
% 1.25/0.52  fof(f266,plain,(
% 1.25/0.52    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f265,f51])).
% 1.25/0.52  fof(f265,plain,(
% 1.25/0.52    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f264,f52])).
% 1.25/0.52  fof(f264,plain,(
% 1.25/0.52    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f263,f254])).
% 1.25/0.52  fof(f254,plain,(
% 1.25/0.52    v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f253,f50])).
% 1.25/0.52  fof(f253,plain,(
% 1.25/0.52    v1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f252,f51])).
% 1.25/0.52  fof(f252,plain,(
% 1.25/0.52    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f227,f52])).
% 1.25/0.52  fof(f227,plain,(
% 1.25/0.52    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f54,f73])).
% 1.25/0.52  fof(f73,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f33])).
% 1.25/0.52  fof(f33,plain,(
% 1.25/0.52    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f32])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f8])).
% 1.25/0.52  fof(f8,axiom,(
% 1.25/0.52    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 1.25/0.52  fof(f263,plain,(
% 1.25/0.52    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f262,f257])).
% 1.25/0.52  fof(f257,plain,(
% 1.25/0.52    v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f256,f50])).
% 1.25/0.52  fof(f256,plain,(
% 1.25/0.52    v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f255,f51])).
% 1.25/0.52  fof(f255,plain,(
% 1.25/0.52    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f228,f52])).
% 1.25/0.52  fof(f228,plain,(
% 1.25/0.52    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f54,f74])).
% 1.25/0.52  fof(f74,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f33])).
% 1.25/0.52  fof(f262,plain,(
% 1.25/0.52    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f261,f260])).
% 1.25/0.52  fof(f260,plain,(
% 1.25/0.52    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f259,f50])).
% 1.25/0.52  fof(f259,plain,(
% 1.25/0.52    l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f258,f51])).
% 1.25/0.52  fof(f258,plain,(
% 1.25/0.52    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f229,f52])).
% 1.25/0.52  fof(f229,plain,(
% 1.25/0.52    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f54,f75])).
% 1.25/0.52  fof(f75,plain,(
% 1.25/0.52    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f33])).
% 1.25/0.52  fof(f261,plain,(
% 1.25/0.52    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f230,f233])).
% 1.25/0.52  fof(f230,plain,(
% 1.25/0.52    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f54,f81])).
% 1.25/0.52  fof(f81,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(equality_resolution,[],[f80])).
% 1.25/0.52  fof(f80,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(equality_resolution,[],[f61])).
% 1.25/0.52  fof(f61,plain,(
% 1.25/0.52    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f45])).
% 1.25/0.52  fof(f45,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 1.25/0.52  fof(f44,plain,(
% 1.25/0.52    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f43,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(rectify,[],[f42])).
% 1.25/0.52  fof(f42,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(nnf_transformation,[],[f23])).
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f22])).
% 1.25/0.52  fof(f22,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f5])).
% 1.25/0.52  fof(f5,axiom,(
% 1.25/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).
% 1.25/0.52  fof(f505,plain,(
% 1.25/0.52    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.25/0.52    inference(subsumption_resolution,[],[f504,f50])).
% 1.25/0.52  fof(f504,plain,(
% 1.25/0.52    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f503,f51])).
% 1.25/0.52  fof(f503,plain,(
% 1.25/0.52    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f484,f52])).
% 1.25/0.52  fof(f484,plain,(
% 1.25/0.52    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f233,f70])).
% 1.25/0.52  fof(f70,plain,(
% 1.25/0.52    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f29])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f28])).
% 1.25/0.52  fof(f28,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f9])).
% 1.25/0.52  fof(f9,axiom,(
% 1.25/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.25/0.52  fof(f498,plain,(
% 1.25/0.52    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 1.25/0.52    inference(forward_demodulation,[],[f497,f267])).
% 1.25/0.52  fof(f497,plain,(
% 1.25/0.52    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))),
% 1.25/0.52    inference(subsumption_resolution,[],[f496,f50])).
% 1.25/0.52  fof(f496,plain,(
% 1.25/0.52    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f495,f51])).
% 1.25/0.52  fof(f495,plain,(
% 1.25/0.52    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f482,f52])).
% 1.25/0.52  fof(f482,plain,(
% 1.25/0.52    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f233,f77])).
% 1.25/0.52  fof(f77,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f35])).
% 1.25/0.52  fof(f1991,plain,(
% 1.25/0.52    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1990,f559])).
% 1.25/0.52  fof(f559,plain,(
% 1.25/0.52    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.25/0.52    inference(backward_demodulation,[],[f529,f558])).
% 1.25/0.52  fof(f529,plain,(
% 1.25/0.52    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.25/0.52    inference(backward_demodulation,[],[f502,f506])).
% 1.25/0.52  fof(f502,plain,(
% 1.25/0.52    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 1.25/0.52    inference(forward_demodulation,[],[f501,f267])).
% 1.25/0.52  fof(f501,plain,(
% 1.25/0.52    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))),
% 1.25/0.52    inference(subsumption_resolution,[],[f500,f50])).
% 1.25/0.52  fof(f500,plain,(
% 1.25/0.52    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f499,f51])).
% 1.25/0.52  fof(f499,plain,(
% 1.25/0.52    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f483,f52])).
% 1.25/0.52  fof(f483,plain,(
% 1.25/0.52    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f233,f78])).
% 1.25/0.52  fof(f78,plain,(
% 1.25/0.52    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f35])).
% 1.25/0.52  fof(f1990,plain,(
% 1.25/0.52    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 1.25/0.52    inference(duplicate_literal_removal,[],[f1989])).
% 1.25/0.52  fof(f1989,plain,(
% 1.25/0.52    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 1.25/0.52    inference(condensation,[],[f1988])).
% 1.25/0.52  fof(f1988,plain,(
% 1.25/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) )),
% 1.25/0.52    inference(duplicate_literal_removal,[],[f1987])).
% 1.25/0.52  fof(f1987,plain,(
% 1.25/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 1.25/0.52    inference(resolution,[],[f1488,f79])).
% 1.25/0.52  fof(f79,plain,(
% 1.25/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f37])).
% 1.25/0.52  fof(f37,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.25/0.52    inference(flattening,[],[f36])).
% 1.25/0.52  fof(f36,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f3])).
% 1.25/0.52  fof(f3,axiom,(
% 1.25/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 1.25/0.52  fof(f1488,plain,(
% 1.25/0.52    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(forward_demodulation,[],[f1487,f506])).
% 1.25/0.52  fof(f1487,plain,(
% 1.25/0.52    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(forward_demodulation,[],[f1486,f267])).
% 1.25/0.52  fof(f1486,plain,(
% 1.25/0.52    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(forward_demodulation,[],[f1485,f558])).
% 1.25/0.52  fof(f1485,plain,(
% 1.25/0.52    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.25/0.52    inference(forward_demodulation,[],[f1484,f1410])).
% 1.25/0.52  fof(f1410,plain,(
% 1.25/0.52    u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1409,f560])).
% 1.25/0.52  fof(f1409,plain,(
% 1.25/0.52    u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1408,f1060])).
% 1.25/0.52  fof(f1060,plain,(
% 1.25/0.52    r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)),
% 1.25/0.52    inference(resolution,[],[f563,f55])).
% 1.25/0.52  fof(f55,plain,(
% 1.25/0.52    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.25/0.52    inference(cnf_transformation,[],[f41])).
% 1.25/0.52  fof(f563,plain,(
% 1.25/0.52    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK1)) | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),X6)) )),
% 1.25/0.52    inference(backward_demodulation,[],[f278,f558])).
% 1.25/0.52  fof(f278,plain,(
% 1.25/0.52    ( ! [X6] : (r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK1))) )),
% 1.25/0.52    inference(forward_demodulation,[],[f277,f267])).
% 1.25/0.52  fof(f277,plain,(
% 1.25/0.52    ( ! [X6] : (r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK1))) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f276,f50])).
% 1.25/0.52  fof(f276,plain,(
% 1.25/0.52    ( ! [X6] : (r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK1)) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f275,f51])).
% 1.25/0.52  fof(f275,plain,(
% 1.25/0.52    ( ! [X6] : (r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f274,f52])).
% 1.25/0.52  fof(f274,plain,(
% 1.25/0.52    ( ! [X6] : (r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f273,f233])).
% 1.25/0.52  fof(f273,plain,(
% 1.25/0.52    ( ! [X6] : (r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f232,f53])).
% 1.25/0.52  fof(f53,plain,(
% 1.25/0.52    ~v2_struct_0(sK1)),
% 1.25/0.52    inference(cnf_transformation,[],[f41])).
% 1.25/0.52  fof(f232,plain,(
% 1.25/0.52    ( ! [X6] : (r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(resolution,[],[f54,f84])).
% 1.25/0.52  fof(f84,plain,(
% 1.25/0.52    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(equality_resolution,[],[f72])).
% 1.25/0.52  fof(f72,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f31])).
% 1.25/0.52  fof(f31,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f30])).
% 1.25/0.52  fof(f30,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f10])).
% 1.25/0.52  fof(f10,axiom,(
% 1.25/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).
% 1.25/0.52  fof(f1408,plain,(
% 1.25/0.52    ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1407,f559])).
% 1.25/0.52  fof(f1407,plain,(
% 1.25/0.52    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(resolution,[],[f537,f562])).
% 1.25/0.52  fof(f537,plain,(
% 1.25/0.52    ( ! [X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))) )),
% 1.25/0.52    inference(forward_demodulation,[],[f512,f506])).
% 1.25/0.52  fof(f512,plain,(
% 1.25/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X1)) )),
% 1.25/0.52    inference(backward_demodulation,[],[f309,f506])).
% 1.25/0.52  fof(f309,plain,(
% 1.25/0.52    ( ! [X1] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X1)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f308,f50])).
% 1.25/0.52  fof(f308,plain,(
% 1.25/0.52    ( ! [X1] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X1) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f307,f51])).
% 1.25/0.52  fof(f307,plain,(
% 1.25/0.52    ( ! [X1] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f306,f52])).
% 1.25/0.52  fof(f306,plain,(
% 1.25/0.52    ( ! [X1] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f288,f54])).
% 1.25/0.52  fof(f288,plain,(
% 1.25/0.52    ( ! [X1] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X1,sK1),sK2) | u1_struct_0(sK1) = sK4(sK0,sK1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(superposition,[],[f56,f67])).
% 1.25/0.52  fof(f67,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK4(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f49])).
% 1.25/0.52  fof(f49,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).
% 1.25/0.52  fof(f48,plain,(
% 1.25/0.52    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f47,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(rectify,[],[f46])).
% 1.25/0.52  fof(f46,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(nnf_transformation,[],[f25])).
% 1.25/0.52  fof(f25,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f24])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,axiom,(
% 1.25/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).
% 1.25/0.52  fof(f56,plain,(
% 1.25/0.52    ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)),
% 1.25/0.52    inference(cnf_transformation,[],[f41])).
% 1.25/0.52  fof(f1484,plain,(
% 1.25/0.52    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1483,f560])).
% 1.25/0.52  fof(f1483,plain,(
% 1.25/0.52    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1482,f1060])).
% 1.25/0.52  % (7444)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.25/0.52  fof(f1482,plain,(
% 1.25/0.52    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f1481,f559])).
% 1.25/0.52  fof(f1481,plain,(
% 1.25/0.52    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(resolution,[],[f539,f562])).
% 1.25/0.52  fof(f539,plain,(
% 1.25/0.52    ( ! [X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))) )),
% 1.25/0.52    inference(forward_demodulation,[],[f538,f506])).
% 1.25/0.52  fof(f538,plain,(
% 1.25/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X2)) )),
% 1.25/0.52    inference(forward_demodulation,[],[f513,f506])).
% 1.25/0.52  fof(f513,plain,(
% 1.25/0.52    ( ! [X2] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X2)) )),
% 1.25/0.52    inference(backward_demodulation,[],[f313,f506])).
% 1.25/0.52  fof(f313,plain,(
% 1.25/0.52    ( ! [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X2)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f312,f50])).
% 1.25/0.52  fof(f312,plain,(
% 1.25/0.52    ( ! [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X2) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f311,f51])).
% 1.25/0.52  fof(f311,plain,(
% 1.25/0.52    ( ! [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f310,f52])).
% 1.25/0.52  fof(f310,plain,(
% 1.25/0.52    ( ! [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f289,f54])).
% 1.25/0.52  fof(f289,plain,(
% 1.25/0.52    ( ! [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),X2,sK1),sK2) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X2))),X2,k7_tmap_1(sK0,sK4(sK0,sK1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.25/0.52    inference(superposition,[],[f56,f68])).
% 1.25/0.52  fof(f68,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f49])).
% 1.25/0.52  % SZS output end Proof for theBenchmark
% 1.25/0.52  % (7431)------------------------------
% 1.25/0.52  % (7431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (7431)Termination reason: Refutation
% 1.25/0.52  
% 1.25/0.52  % (7431)Memory used [KB]: 2686
% 1.25/0.52  % (7431)Time elapsed: 0.094 s
% 1.25/0.52  % (7431)------------------------------
% 1.25/0.52  % (7431)------------------------------
% 1.25/0.52  % (7426)Success in time 0.162 s
%------------------------------------------------------------------------------
