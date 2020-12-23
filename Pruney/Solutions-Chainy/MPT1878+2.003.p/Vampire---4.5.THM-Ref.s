%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:43 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 326 expanded)
%              Number of leaves         :   19 (  99 expanded)
%              Depth                    :   21
%              Number of atoms          :  353 (1678 expanded)
%              Number of equality atoms :   39 (  39 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f414,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f413])).

fof(f413,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f402,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f402,plain,(
    ! [X0] : k1_xboole_0 != k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f69,f391])).

fof(f391,plain,(
    k1_xboole_0 = k1_tarski(sK4(sK3(sK0))) ),
    inference(resolution,[],[f389,f277])).

fof(f277,plain,(
    m1_subset_1(sK4(sK3(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f163,f106])).

fof(f106,plain,(
    r2_hidden(sK4(sK3(sK0)),sK3(sK0)) ),
    inference(resolution,[],[f96,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f96,plain,(
    ~ v1_xboole_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f95,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( v3_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( v3_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_xboole_0(X1) )
   => ( v3_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f95,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f49,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f163,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3(sK0))
      | m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f94,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f93,f47])).

fof(f93,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f89,f48])).

fof(f89,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f49,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f389,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(subsumption_resolution,[],[f388,f174])).

fof(f174,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f164,f96])).

fof(f164,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f94,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f388,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_tarski(X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_tarski(X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f223,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f223,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_domain_1(u1_struct_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f222,f92])).

fof(f92,plain,(
    ! [X7] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X7),sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f91,plain,(
    ! [X7] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X7),sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f48])).

fof(f88,plain,(
    ! [X7] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X7),sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f49,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f222,plain,(
    ! [X0] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | k1_xboole_0 = k6_domain_1(u1_struct_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f217,f174])).

fof(f217,plain,(
    ! [X0] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | k1_xboole_0 = k6_domain_1(u1_struct_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f140,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f139,f49])).

fof(f139,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f138,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f134,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f134,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f127,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f127,plain,(
    v3_tex_2(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f52,f99])).

fof(f99,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f50,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f50,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:53:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (32123)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (32123)Refutation not found, incomplete strategy% (32123)------------------------------
% 0.22/0.53  % (32123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32123)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32123)Memory used [KB]: 6140
% 0.22/0.53  % (32123)Time elapsed: 0.084 s
% 0.22/0.53  % (32123)------------------------------
% 0.22/0.53  % (32123)------------------------------
% 0.22/0.53  % (32132)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (32120)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (32130)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.56  % (32129)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  % (32118)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.56  % (32119)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (32124)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.56  % (32118)Refutation not found, incomplete strategy% (32118)------------------------------
% 0.22/0.56  % (32118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32118)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32118)Memory used [KB]: 10618
% 0.22/0.56  % (32118)Time elapsed: 0.124 s
% 0.22/0.56  % (32118)------------------------------
% 0.22/0.56  % (32118)------------------------------
% 0.22/0.57  % (32121)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.70/0.58  % (32136)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.70/0.58  % (32131)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.70/0.58  % (32124)Refutation not found, incomplete strategy% (32124)------------------------------
% 1.70/0.58  % (32124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (32124)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.58  
% 1.70/0.58  % (32124)Memory used [KB]: 10618
% 1.70/0.58  % (32124)Time elapsed: 0.128 s
% 1.70/0.58  % (32124)------------------------------
% 1.70/0.58  % (32124)------------------------------
% 1.70/0.58  % (32131)Refutation not found, incomplete strategy% (32131)------------------------------
% 1.70/0.58  % (32131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (32131)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.58  
% 1.70/0.58  % (32131)Memory used [KB]: 6140
% 1.70/0.58  % (32131)Time elapsed: 0.146 s
% 1.70/0.58  % (32131)------------------------------
% 1.70/0.58  % (32131)------------------------------
% 1.70/0.58  % (32142)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.70/0.59  % (32135)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.70/0.59  % (32138)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.70/0.59  % (32136)Refutation found. Thanks to Tanya!
% 1.70/0.59  % SZS status Theorem for theBenchmark
% 1.70/0.59  % SZS output start Proof for theBenchmark
% 1.70/0.59  fof(f414,plain,(
% 1.70/0.59    $false),
% 1.70/0.59    inference(trivial_inequality_removal,[],[f413])).
% 1.70/0.59  fof(f413,plain,(
% 1.70/0.59    k1_xboole_0 != k1_xboole_0),
% 1.70/0.59    inference(superposition,[],[f402,f55])).
% 1.70/0.59  fof(f55,plain,(
% 1.70/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f3])).
% 1.70/0.59  fof(f3,axiom,(
% 1.70/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.70/0.59  fof(f402,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,X0)) )),
% 1.70/0.59    inference(superposition,[],[f69,f391])).
% 1.70/0.59  fof(f391,plain,(
% 1.70/0.59    k1_xboole_0 = k1_tarski(sK4(sK3(sK0)))),
% 1.70/0.59    inference(resolution,[],[f389,f277])).
% 1.70/0.59  fof(f277,plain,(
% 1.70/0.59    m1_subset_1(sK4(sK3(sK0)),u1_struct_0(sK0))),
% 1.70/0.59    inference(resolution,[],[f163,f106])).
% 1.70/0.59  fof(f106,plain,(
% 1.70/0.59    r2_hidden(sK4(sK3(sK0)),sK3(sK0))),
% 1.70/0.59    inference(resolution,[],[f96,f68])).
% 1.70/0.59  fof(f68,plain,(
% 1.70/0.59    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f46])).
% 1.70/0.59  fof(f46,plain,(
% 1.70/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 1.70/0.59  fof(f45,plain,(
% 1.70/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f44,plain,(
% 1.70/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.70/0.59    inference(rectify,[],[f43])).
% 1.70/0.59  fof(f43,plain,(
% 1.70/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.70/0.59    inference(nnf_transformation,[],[f1])).
% 1.70/0.59  fof(f1,axiom,(
% 1.70/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.70/0.59  fof(f96,plain,(
% 1.70/0.59    ~v1_xboole_0(sK3(sK0))),
% 1.70/0.59    inference(subsumption_resolution,[],[f95,f47])).
% 1.70/0.59  fof(f47,plain,(
% 1.70/0.59    ~v2_struct_0(sK0)),
% 1.70/0.59    inference(cnf_transformation,[],[f35])).
% 1.70/0.59  fof(f35,plain,(
% 1.70/0.59    (v3_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f34,f33])).
% 1.70/0.59  fof(f33,plain,(
% 1.70/0.59    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f34,plain,(
% 1.70/0.59    ? [X1] : (v3_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) => (v3_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f18,plain,(
% 1.70/0.59    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.59    inference(flattening,[],[f17])).
% 1.70/0.59  fof(f17,plain,(
% 1.70/0.59    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f15])).
% 1.70/0.59  fof(f15,negated_conjecture,(
% 1.70/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.70/0.59    inference(negated_conjecture,[],[f14])).
% 1.70/0.59  fof(f14,conjecture,(
% 1.70/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 1.70/0.59  fof(f95,plain,(
% 1.70/0.59    ~v1_xboole_0(sK3(sK0)) | v2_struct_0(sK0)),
% 1.70/0.59    inference(subsumption_resolution,[],[f90,f48])).
% 1.70/0.59  fof(f48,plain,(
% 1.70/0.59    v2_pre_topc(sK0)),
% 1.70/0.59    inference(cnf_transformation,[],[f35])).
% 1.70/0.59  fof(f90,plain,(
% 1.70/0.59    ~v1_xboole_0(sK3(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.59    inference(resolution,[],[f49,f66])).
% 1.70/0.59  fof(f66,plain,(
% 1.70/0.59    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f42])).
% 1.70/0.59  fof(f42,plain,(
% 1.70/0.59    ! [X0] : ((~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f41])).
% 1.70/0.59  fof(f41,plain,(
% 1.70/0.59    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f26,plain,(
% 1.70/0.59    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.59    inference(flattening,[],[f25])).
% 1.70/0.59  fof(f25,plain,(
% 1.70/0.59    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f16])).
% 1.70/0.59  fof(f16,plain,(
% 1.70/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.70/0.59    inference(pure_predicate_removal,[],[f9])).
% 1.70/0.59  fof(f9,axiom,(
% 1.70/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).
% 1.70/0.59  fof(f49,plain,(
% 1.70/0.59    l1_pre_topc(sK0)),
% 1.70/0.59    inference(cnf_transformation,[],[f35])).
% 1.70/0.59  fof(f163,plain,(
% 1.70/0.59    ( ! [X2] : (~r2_hidden(X2,sK3(sK0)) | m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.70/0.59    inference(resolution,[],[f94,f72])).
% 1.70/0.59  fof(f72,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f32])).
% 1.70/0.59  fof(f32,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.70/0.59    inference(flattening,[],[f31])).
% 1.70/0.59  fof(f31,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.70/0.59    inference(ennf_transformation,[],[f8])).
% 1.70/0.59  fof(f8,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.70/0.59  fof(f94,plain,(
% 1.70/0.59    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.59    inference(subsumption_resolution,[],[f93,f47])).
% 1.70/0.59  fof(f93,plain,(
% 1.70/0.59    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.70/0.59    inference(subsumption_resolution,[],[f89,f48])).
% 1.70/0.59  fof(f89,plain,(
% 1.70/0.59    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.59    inference(resolution,[],[f49,f65])).
% 1.70/0.59  fof(f65,plain,(
% 1.70/0.59    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f42])).
% 1.70/0.59  fof(f389,plain,(
% 1.70/0.59    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k1_tarski(X1)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f388,f174])).
% 1.70/0.59  fof(f174,plain,(
% 1.70/0.59    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.70/0.59    inference(subsumption_resolution,[],[f164,f96])).
% 1.70/0.59  fof(f164,plain,(
% 1.70/0.59    v1_xboole_0(sK3(sK0)) | ~v1_xboole_0(u1_struct_0(sK0))),
% 1.70/0.59    inference(resolution,[],[f94,f63])).
% 1.70/0.59  fof(f63,plain,(
% 1.70/0.59    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f22])).
% 1.70/0.59  fof(f22,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f7])).
% 1.70/0.59  fof(f7,axiom,(
% 1.70/0.59    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.70/0.59  fof(f388,plain,(
% 1.70/0.59    ( ! [X1] : (k1_xboole_0 = k1_tarski(X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 1.70/0.59    inference(duplicate_literal_removal,[],[f379])).
% 1.70/0.59  fof(f379,plain,(
% 1.70/0.59    ( ! [X1] : (k1_xboole_0 = k1_tarski(X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 1.70/0.59    inference(superposition,[],[f223,f70])).
% 1.70/0.59  fof(f70,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f28])).
% 1.70/0.59  fof(f28,plain,(
% 1.70/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.70/0.59    inference(flattening,[],[f27])).
% 1.70/0.59  fof(f27,plain,(
% 1.70/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f11])).
% 1.70/0.59  fof(f11,axiom,(
% 1.70/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.70/0.59  fof(f223,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 = k6_domain_1(u1_struct_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f222,f92])).
% 1.70/0.59  fof(f92,plain,(
% 1.70/0.59    ( ! [X7] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X7),sK0) | ~m1_subset_1(X7,u1_struct_0(sK0))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f91,f47])).
% 1.70/0.59  fof(f91,plain,(
% 1.70/0.59    ( ! [X7] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X7),sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f88,f48])).
% 1.70/0.59  fof(f88,plain,(
% 1.70/0.59    ( ! [X7] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X7),sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.59    inference(resolution,[],[f49,f64])).
% 1.70/0.59  fof(f64,plain,(
% 1.70/0.59    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f24])).
% 1.70/0.59  fof(f24,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.59    inference(flattening,[],[f23])).
% 1.70/0.59  fof(f23,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f13])).
% 1.70/0.59  fof(f13,axiom,(
% 1.70/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 1.70/0.59  fof(f222,plain,(
% 1.70/0.59    ( ! [X0] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | k1_xboole_0 = k6_domain_1(u1_struct_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f217,f174])).
% 1.70/0.59  fof(f217,plain,(
% 1.70/0.59    ( ! [X0] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | k1_xboole_0 = k6_domain_1(u1_struct_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 1.70/0.59    inference(resolution,[],[f140,f71])).
% 1.70/0.59  fof(f71,plain,(
% 1.70/0.59    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f30,plain,(
% 1.70/0.59    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.70/0.59    inference(flattening,[],[f29])).
% 1.70/0.59  fof(f29,plain,(
% 1.70/0.59    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f10])).
% 1.70/0.59  fof(f10,axiom,(
% 1.70/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.70/0.59  fof(f140,plain,(
% 1.70/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | k1_xboole_0 = X0) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f139,f49])).
% 1.70/0.59  fof(f139,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f138,f54])).
% 1.70/0.59  fof(f54,plain,(
% 1.70/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f6])).
% 1.70/0.59  fof(f6,axiom,(
% 1.70/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.70/0.59  fof(f138,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f134,f53])).
% 1.70/0.59  fof(f53,plain,(
% 1.70/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f4])).
% 1.70/0.59  fof(f4,axiom,(
% 1.70/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.70/0.59  fof(f134,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.70/0.59    inference(resolution,[],[f127,f57])).
% 1.70/0.59  fof(f57,plain,(
% 1.70/0.59    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f40])).
% 1.70/0.59  fof(f40,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 1.70/0.59  fof(f39,plain,(
% 1.70/0.59    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f38,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(rectify,[],[f37])).
% 1.70/0.59  fof(f37,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(flattening,[],[f36])).
% 1.70/0.59  fof(f36,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(nnf_transformation,[],[f20])).
% 1.70/0.59  fof(f20,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(flattening,[],[f19])).
% 1.70/0.59  fof(f19,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f12])).
% 1.70/0.59  fof(f12,axiom,(
% 1.70/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.70/0.59  fof(f127,plain,(
% 1.70/0.59    v3_tex_2(k1_xboole_0,sK0)),
% 1.70/0.59    inference(backward_demodulation,[],[f52,f99])).
% 1.70/0.59  fof(f99,plain,(
% 1.70/0.59    k1_xboole_0 = sK1),
% 1.70/0.59    inference(resolution,[],[f50,f62])).
% 1.70/0.59  fof(f62,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f21])).
% 1.70/0.59  fof(f21,plain,(
% 1.70/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f2])).
% 1.70/0.59  fof(f2,axiom,(
% 1.70/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.70/0.59  fof(f50,plain,(
% 1.70/0.59    v1_xboole_0(sK1)),
% 1.70/0.59    inference(cnf_transformation,[],[f35])).
% 1.70/0.59  fof(f52,plain,(
% 1.70/0.59    v3_tex_2(sK1,sK0)),
% 1.70/0.59    inference(cnf_transformation,[],[f35])).
% 1.70/0.59  fof(f69,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f5])).
% 1.70/0.59  fof(f5,axiom,(
% 1.70/0.59    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.70/0.59  % SZS output end Proof for theBenchmark
% 1.70/0.59  % (32136)------------------------------
% 1.70/0.59  % (32136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (32136)Termination reason: Refutation
% 1.70/0.59  
% 1.70/0.59  % (32136)Memory used [KB]: 1791
% 1.70/0.59  % (32136)Time elapsed: 0.159 s
% 1.70/0.59  % (32136)------------------------------
% 1.70/0.59  % (32136)------------------------------
% 1.70/0.59  % (32117)Success in time 0.227 s
%------------------------------------------------------------------------------
