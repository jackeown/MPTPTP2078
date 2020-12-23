%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  148 (3288 expanded)
%              Number of leaves         :   19 ( 824 expanded)
%              Depth                    :   50
%              Number of atoms          :  559 (18167 expanded)
%              Number of equality atoms :  111 ( 929 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f387,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f355,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f355,plain,(
    ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f342,f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f71,f70])).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f342,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f193,f323])).

fof(f323,plain,(
    u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(backward_demodulation,[],[f146,f299])).

fof(f299,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(backward_demodulation,[],[f235,f293])).

fof(f293,plain,(
    sK1 = sK2(u1_struct_0(sK0)) ),
    inference(resolution,[],[f292,f67])).

fof(f292,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK2(u1_struct_0(sK0)) = X0 ) ),
    inference(subsumption_resolution,[],[f291,f66])).

fof(f291,plain,(
    ! [X0] :
      ( sK2(u1_struct_0(sK0)) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f289,f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f289,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | sK2(u1_struct_0(sK0)) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f287,f65])).

fof(f287,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK2(u1_struct_0(sK0)) = X0
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f265,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f265,plain,(
    ! [X1] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK2(u1_struct_0(sK0)) = X1 ) ),
    inference(superposition,[],[f111,f236])).

fof(f236,plain,(
    u1_struct_0(sK0) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f223,f235])).

fof(f223,plain,(
    u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f222,f219])).

fof(f219,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f218,f65])).

fof(f218,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f66])).

fof(f216,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f214,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f135,f92])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f134,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f105,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f214,plain,(
    m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f213,f66])).

fof(f213,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f212,f77])).

fof(f212,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f210,f65])).

fof(f210,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f208,f84])).

fof(f208,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f203,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f203,plain,(
    v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f202,f66])).

fof(f202,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f201,f77])).

fof(f201,plain,
    ( ~ l1_struct_0(sK0)
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f199,f65])).

fof(f199,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f183,f84])).

fof(f183,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f182,f127])).

fof(f127,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f125,f67])).

fof(f125,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f87,f122])).

fof(f122,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f121,f66])).

fof(f121,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f120,f65])).

fof(f120,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f119,f67])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f112,f77])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f99,f84])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f93,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(f182,plain,(
    ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f181,f124])).

fof(f124,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f69,f122])).

fof(f69,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f181,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f180,f65])).

fof(f180,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f67])).

fof(f179,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f66])).

fof(f178,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f152,f92])).

fof(f152,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X7)
      | v1_tex_2(k1_tex_2(sK0,sK1),X7)
      | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(X7))
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f115,f146])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f82,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f222,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f221,f66])).

fof(f221,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f217,f65])).

fof(f217,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f214,f119])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k2_tarski(X1,X1))
      | v1_xboole_0(k2_tarski(X1,X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f108,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f108,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f94,f72])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f235,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f234,f66])).

fof(f234,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f233,f77])).

fof(f233,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f231,f65])).

fof(f231,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f220,f84])).

fof(f220,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f207,f219])).

fof(f207,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f203,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f146,plain,(
    k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(forward_demodulation,[],[f145,f122])).

fof(f145,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f144,f65])).

fof(f144,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f143,f66])).

fof(f143,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f136,f67])).

fof(f193,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f192,f182])).

fof(f192,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f191,f146])).

fof(f191,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f190,f146])).

fof(f190,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f188,f66])).

fof(f188,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f184,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f184,plain,(
    v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f182,f123])).

fof(f123,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f68,f122])).

fof(f68,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f67,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (24938)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.50  % (24948)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (24940)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.50  % (24954)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.50  % (24926)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.50  % (24928)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.50  % (24932)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (24933)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.51  % (24946)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.51  % (24938)Refutation not found, incomplete strategy% (24938)------------------------------
% 0.19/0.51  % (24938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (24938)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (24938)Memory used [KB]: 10618
% 0.19/0.51  % (24938)Time elapsed: 0.112 s
% 0.19/0.51  % (24938)------------------------------
% 0.19/0.51  % (24938)------------------------------
% 0.19/0.51  % (24930)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.52  % (24954)Refutation not found, incomplete strategy% (24954)------------------------------
% 0.19/0.52  % (24954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (24954)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (24954)Memory used [KB]: 10746
% 0.19/0.52  % (24954)Time elapsed: 0.116 s
% 0.19/0.52  % (24954)------------------------------
% 0.19/0.52  % (24954)------------------------------
% 0.19/0.52  % (24936)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.52  % (24948)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f387,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f65,f66,f67,f355,f92])).
% 0.19/0.52  fof(f92,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f43])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.52    inference(flattening,[],[f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,axiom,(
% 0.19/0.52    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.19/0.52  fof(f355,plain,(
% 0.19/0.52    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f342,f109])).
% 0.19/0.52  fof(f109,plain,(
% 0.19/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f71,f70])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.19/0.52  fof(f342,plain,(
% 0.19/0.52    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.52    inference(backward_demodulation,[],[f193,f323])).
% 0.19/0.52  fof(f323,plain,(
% 0.19/0.52    u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.19/0.52    inference(backward_demodulation,[],[f146,f299])).
% 0.19/0.52  fof(f299,plain,(
% 0.19/0.52    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.19/0.52    inference(backward_demodulation,[],[f235,f293])).
% 0.19/0.52  fof(f293,plain,(
% 0.19/0.52    sK1 = sK2(u1_struct_0(sK0))),
% 0.19/0.52    inference(resolution,[],[f292,f67])).
% 0.19/0.52  fof(f292,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2(u1_struct_0(sK0)) = X0) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f291,f66])).
% 0.19/0.52  fof(f291,plain,(
% 0.19/0.52    ( ! [X0] : (sK2(u1_struct_0(sK0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0)) )),
% 0.19/0.52    inference(resolution,[],[f289,f77])).
% 0.19/0.52  fof(f77,plain,(
% 0.19/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.52  fof(f289,plain,(
% 0.19/0.52    ( ! [X0] : (~l1_struct_0(sK0) | sK2(u1_struct_0(sK0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f287,f65])).
% 0.19/0.52  fof(f287,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2(u1_struct_0(sK0)) = X0 | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.52    inference(resolution,[],[f265,f84])).
% 0.19/0.52  fof(f84,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.52    inference(flattening,[],[f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,axiom,(
% 0.19/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.52  fof(f265,plain,(
% 0.19/0.52    ( ! [X1] : (v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK2(u1_struct_0(sK0)) = X1) )),
% 0.19/0.52    inference(superposition,[],[f111,f236])).
% 0.19/0.52  fof(f236,plain,(
% 0.19/0.52    u1_struct_0(sK0) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))),
% 0.19/0.52    inference(backward_demodulation,[],[f223,f235])).
% 0.19/0.52  fof(f223,plain,(
% 0.19/0.52    u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))),
% 0.19/0.52    inference(forward_demodulation,[],[f222,f219])).
% 0.19/0.52  fof(f219,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0))))),
% 0.19/0.52    inference(subsumption_resolution,[],[f218,f65])).
% 0.19/0.52  fof(f218,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) | v2_struct_0(sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f216,f66])).
% 0.19/0.52  fof(f216,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.52    inference(resolution,[],[f214,f136])).
% 0.19/0.52  fof(f136,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f135,f92])).
% 0.19/0.52  fof(f135,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_pre_topc(k1_tex_2(X0,X1),X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f134,f90])).
% 0.19/0.52  fof(f90,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f43])).
% 0.19/0.52  fof(f134,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_pre_topc(k1_tex_2(X0,X1),X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f133])).
% 0.19/0.52  fof(f133,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_pre_topc(k1_tex_2(X0,X1),X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(resolution,[],[f105,f91])).
% 0.19/0.52  fof(f91,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f43])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f85])).
% 0.19/0.52  fof(f85,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.52    inference(flattening,[],[f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,axiom,(
% 0.19/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 0.19/0.52  fof(f214,plain,(
% 0.19/0.52    m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f213,f66])).
% 0.19/0.52  fof(f213,plain,(
% 0.19/0.52    m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.19/0.52    inference(resolution,[],[f212,f77])).
% 0.19/0.52  fof(f212,plain,(
% 0.19/0.52    ~l1_struct_0(sK0) | m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f210,f65])).
% 0.19/0.52  fof(f210,plain,(
% 0.19/0.52    m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.19/0.52    inference(resolution,[],[f208,f84])).
% 0.19/0.52  fof(f208,plain,(
% 0.19/0.52    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.19/0.52    inference(resolution,[],[f203,f73])).
% 0.19/0.52  fof(f73,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_zfmisc_1(X0) | m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f55])).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.19/0.52    inference(rectify,[],[f52])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.19/0.52  fof(f203,plain,(
% 0.19/0.52    v1_zfmisc_1(u1_struct_0(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f202,f66])).
% 0.19/0.52  fof(f202,plain,(
% 0.19/0.52    v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.19/0.52    inference(resolution,[],[f201,f77])).
% 0.19/0.52  fof(f201,plain,(
% 0.19/0.52    ~l1_struct_0(sK0) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f199,f65])).
% 0.19/0.52  fof(f199,plain,(
% 0.19/0.52    v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.19/0.52    inference(resolution,[],[f183,f84])).
% 0.19/0.52  fof(f183,plain,(
% 0.19/0.52    v1_xboole_0(u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.19/0.52    inference(resolution,[],[f182,f127])).
% 0.19/0.52  fof(f127,plain,(
% 0.19/0.52    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f125,f67])).
% 0.19/0.52  fof(f125,plain,(
% 0.19/0.52    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.52    inference(superposition,[],[f87,f122])).
% 0.19/0.52  fof(f122,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f121,f66])).
% 0.19/0.52  fof(f121,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~l1_pre_topc(sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f120,f65])).
% 0.19/0.52  fof(f120,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.52    inference(resolution,[],[f119,f67])).
% 0.19/0.52  fof(f119,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0) | v2_struct_0(X1) | ~l1_pre_topc(X1)) )),
% 0.19/0.52    inference(resolution,[],[f112,f77])).
% 0.19/0.52  fof(f112,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~l1_struct_0(X1) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1)) )),
% 0.19/0.52    inference(resolution,[],[f99,f84])).
% 0.19/0.52  fof(f99,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.19/0.52    inference(definition_unfolding,[],[f93,f72])).
% 0.19/0.52  fof(f72,plain,(
% 0.19/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.52  fof(f93,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.52    inference(flattening,[],[f44])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.19/0.52  fof(f87,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.19/0.52    inference(flattening,[],[f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,axiom,(
% 0.19/0.52    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).
% 0.19/0.52  fof(f182,plain,(
% 0.19/0.52    ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f181,f124])).
% 0.19/0.52  fof(f124,plain,(
% 0.19/0.52    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))),
% 0.19/0.52    inference(backward_demodulation,[],[f69,f122])).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f51])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.52    inference(flattening,[],[f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.52    inference(flattening,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,negated_conjecture,(
% 0.19/0.52    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.19/0.52    inference(negated_conjecture,[],[f19])).
% 0.19/0.52  fof(f19,conjecture,(
% 0.19/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.19/0.52  fof(f181,plain,(
% 0.19/0.52    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f180,f65])).
% 0.19/0.52  fof(f180,plain,(
% 0.19/0.52    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f179,f67])).
% 0.19/0.52  fof(f179,plain,(
% 0.19/0.52    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f178,f66])).
% 0.19/0.52  fof(f178,plain,(
% 0.19/0.52    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f177])).
% 0.19/0.52  fof(f177,plain,(
% 0.19/0.52    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.52    inference(resolution,[],[f152,f92])).
% 0.19/0.52  fof(f152,plain,(
% 0.19/0.52    ( ! [X7] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X7) | v1_tex_2(k1_tex_2(sK0,sK1),X7) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(X7)) | ~l1_pre_topc(X7)) )),
% 0.19/0.52    inference(superposition,[],[f115,f146])).
% 0.19/0.52  fof(f115,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f114])).
% 0.19/0.52  fof(f114,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(superposition,[],[f82,f81])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ( ! [X0,X1] : (u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f59])).
% 0.19/0.52  fof(f59,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f57,f58])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(rectify,[],[f56])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,axiom,(
% 0.19/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.19/0.52  fof(f82,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f59])).
% 0.19/0.52  fof(f222,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))),
% 0.19/0.52    inference(subsumption_resolution,[],[f221,f66])).
% 0.19/0.52  fof(f221,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f217,f65])).
% 0.19/0.52  fof(f217,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = k2_tarski(sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.52    inference(resolution,[],[f214,f119])).
% 0.19/0.52  fof(f111,plain,(
% 0.19/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k2_tarski(X1,X1)) | v1_xboole_0(k2_tarski(X1,X1)) | X1 = X2) )),
% 0.19/0.52    inference(resolution,[],[f108,f89])).
% 0.19/0.52  fof(f89,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f41])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.52    inference(flattening,[],[f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.52  fof(f108,plain,(
% 0.19/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.19/0.52    inference(equality_resolution,[],[f103])).
% 0.19/0.52  fof(f103,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.19/0.52    inference(definition_unfolding,[],[f94,f72])).
% 0.19/0.52  fof(f94,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f64])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f62,f63])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(rectify,[],[f61])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(nnf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.52  fof(f235,plain,(
% 0.19/0.52    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0))))),
% 0.19/0.52    inference(subsumption_resolution,[],[f234,f66])).
% 0.19/0.52  fof(f234,plain,(
% 0.19/0.52    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.19/0.52    inference(resolution,[],[f233,f77])).
% 0.19/0.52  fof(f233,plain,(
% 0.19/0.52    ~l1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0))))),
% 0.19/0.52    inference(subsumption_resolution,[],[f231,f65])).
% 0.19/0.52  fof(f231,plain,(
% 0.19/0.52    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0)))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.19/0.52    inference(resolution,[],[f220,f84])).
% 0.19/0.52  fof(f220,plain,(
% 0.19/0.52    v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK2(u1_struct_0(sK0))))),
% 0.19/0.52    inference(backward_demodulation,[],[f207,f219])).
% 0.19/0.52  fof(f207,plain,(
% 0.19/0.52    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.52    inference(resolution,[],[f203,f74])).
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f55])).
% 0.19/0.52  fof(f146,plain,(
% 0.19/0.52    k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.19/0.52    inference(forward_demodulation,[],[f145,f122])).
% 0.19/0.52  fof(f145,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.19/0.52    inference(subsumption_resolution,[],[f144,f65])).
% 0.19/0.52  fof(f144,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f143,f66])).
% 0.19/0.52  fof(f143,plain,(
% 0.19/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.52    inference(resolution,[],[f136,f67])).
% 0.19/0.52  fof(f193,plain,(
% 0.19/0.52    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f192,f182])).
% 0.19/0.53  fof(f192,plain,(
% 0.19/0.53    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.53    inference(forward_demodulation,[],[f191,f146])).
% 0.19/0.53  fof(f191,plain,(
% 0.19/0.53    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.53    inference(forward_demodulation,[],[f190,f146])).
% 0.19/0.53  fof(f190,plain,(
% 0.19/0.53    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.53    inference(subsumption_resolution,[],[f188,f66])).
% 0.19/0.53  fof(f188,plain,(
% 0.19/0.53    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.53    inference(resolution,[],[f184,f104])).
% 0.19/0.53  fof(f104,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f79])).
% 0.19/0.53  fof(f79,plain,(
% 0.19/0.53    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f59])).
% 0.19/0.53  fof(f184,plain,(
% 0.19/0.53    v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.53    inference(resolution,[],[f182,f123])).
% 0.19/0.53  fof(f123,plain,(
% 0.19/0.53    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.53    inference(backward_demodulation,[],[f68,f122])).
% 0.19/0.53  fof(f68,plain,(
% 0.19/0.53    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f51])).
% 0.19/0.53  fof(f67,plain,(
% 0.19/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.53    inference(cnf_transformation,[],[f51])).
% 0.19/0.53  fof(f66,plain,(
% 0.19/0.53    l1_pre_topc(sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f51])).
% 0.19/0.53  fof(f65,plain,(
% 0.19/0.53    ~v2_struct_0(sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f51])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (24948)------------------------------
% 0.19/0.53  % (24948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (24948)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (24948)Memory used [KB]: 6524
% 0.19/0.53  % (24948)Time elapsed: 0.074 s
% 0.19/0.53  % (24948)------------------------------
% 0.19/0.53  % (24948)------------------------------
% 0.19/0.53  % (24925)Success in time 0.173 s
%------------------------------------------------------------------------------
