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
% DateTime   : Thu Dec  3 13:21:48 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 706 expanded)
%              Number of leaves         :   21 ( 216 expanded)
%              Depth                    :   19
%              Number of atoms          :  365 (3484 expanded)
%              Number of equality atoms :   31 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f405,f62])).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f405,plain,(
    ! [X0] : k1_xboole_0 != k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f80,f394])).

fof(f394,plain,(
    k1_xboole_0 = k1_tarski(sK7(sK6(sK3))) ),
    inference(subsumption_resolution,[],[f387,f333])).

fof(f333,plain,(
    m1_subset_1(k1_tarski(sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f332,f194])).

fof(f194,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f155,f110])).

fof(f110,plain,(
    r2_hidden(sK7(sK6(sK3)),sK6(sK3)) ),
    inference(resolution,[],[f101,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f101,plain,(
    ~ v1_xboole_0(sK6(sK3)) ),
    inference(subsumption_resolution,[],[f100,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( v3_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( v3_tex_2(X1,sK3)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & v1_xboole_0(X1) )
   => ( v3_tex_2(sK4,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & v1_xboole_0(sK4) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f100,plain,
    ( ~ v1_xboole_0(sK6(sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f95,f55])).

fof(f55,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,
    ( ~ v1_xboole_0(sK6(sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK6(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f56,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f155,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK6(sK3))
      | ~ v1_xboole_0(u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f99,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f99,plain,(
    m1_subset_1(sK6(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f98,f54])).

fof(f98,plain,
    ( m1_subset_1(sK6(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f94,f55])).

fof(f94,plain,
    ( m1_subset_1(sK6(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f56,f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f332,plain,
    ( m1_subset_1(k1_tarski(sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f329,f250])).

fof(f250,plain,(
    m1_subset_1(sK7(sK6(sK3)),u1_struct_0(sK3)) ),
    inference(resolution,[],[f156,f110])).

fof(f156,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK6(sK3))
      | m1_subset_1(X2,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f99,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f329,plain,
    ( m1_subset_1(k1_tarski(sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7(sK6(sK3)),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(superposition,[],[f260,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f260,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f255,f194])).

fof(f255,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f250,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

% (4318)Refutation not found, incomplete strategy% (4318)------------------------------
% (4318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (4318)Termination reason: Refutation not found, incomplete strategy

% (4318)Memory used [KB]: 10618
% (4318)Time elapsed: 0.118 s
% (4318)------------------------------
% (4318)------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f387,plain,
    ( k1_xboole_0 = k1_tarski(sK7(sK6(sK3)))
    | ~ m1_subset_1(k1_tarski(sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f147,f272])).

fof(f272,plain,(
    v2_tex_2(k1_tarski(sK7(sK6(sK3))),sK3) ),
    inference(subsumption_resolution,[],[f271,f194])).

fof(f271,plain,
    ( v2_tex_2(k1_tarski(sK7(sK6(sK3))),sK3)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f270,f250])).

fof(f270,plain,
    ( v2_tex_2(k1_tarski(sK7(sK6(sK3))),sK3)
    | ~ m1_subset_1(sK7(sK6(sK3)),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(superposition,[],[f253,f81])).

fof(f253,plain,(
    v2_tex_2(k6_domain_1(u1_struct_0(sK3),sK7(sK6(sK3))),sK3) ),
    inference(resolution,[],[f250,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) ) ),
    inference(subsumption_resolution,[],[f102,f54])).

fof(f102,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f96,f55])).

fof(f96,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f56,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f147,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK3)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f144,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f144,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_tex_2(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f137,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != X0
          & r1_tarski(X0,sK5(X0,X1))
          & v2_tex_2(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK5(X0,X1) != X0
        & r1_tarski(X0,sK5(X0,X1))
        & v2_tex_2(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f137,plain,(
    sP0(k1_xboole_0,sK3) ),
    inference(resolution,[],[f135,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f135,plain,(
    sP1(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f132,f121])).

fof(f121,plain,(
    v3_tex_2(k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f59,f106])).

fof(f106,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f57,f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f57,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f132,plain,
    ( sP1(sK3,k1_xboole_0)
    | ~ v3_tex_2(k1_xboole_0,sK3) ),
    inference(resolution,[],[f129,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v3_tex_2(X0,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f129,plain,(
    sP2(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f117,f106])).

fof(f117,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f111,f56])).

fof(f111,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f58,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f35,f34,f33])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:35:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (4316)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (4317)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (4317)Refutation not found, incomplete strategy% (4317)------------------------------
% 0.22/0.50  % (4317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4317)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (4317)Memory used [KB]: 6140
% 0.22/0.50  % (4317)Time elapsed: 0.095 s
% 0.22/0.50  % (4317)------------------------------
% 0.22/0.50  % (4317)------------------------------
% 0.22/0.51  % (4334)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (4312)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (4325)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (4325)Refutation not found, incomplete strategy% (4325)------------------------------
% 0.22/0.51  % (4325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (4333)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.18/0.52  % (4325)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (4325)Memory used [KB]: 6140
% 1.18/0.52  % (4325)Time elapsed: 0.101 s
% 1.18/0.52  % (4325)------------------------------
% 1.18/0.52  % (4325)------------------------------
% 1.18/0.52  % (4326)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.18/0.52  % (4320)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.18/0.52  % (4315)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.18/0.52  % (4319)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.18/0.53  % (4312)Refutation not found, incomplete strategy% (4312)------------------------------
% 1.18/0.53  % (4312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (4312)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (4324)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.18/0.53  % (4312)Memory used [KB]: 10618
% 1.18/0.53  % (4312)Time elapsed: 0.094 s
% 1.18/0.53  % (4312)------------------------------
% 1.18/0.53  % (4312)------------------------------
% 1.18/0.53  % (4337)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.18/0.53  % (4314)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.18/0.53  % (4328)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.36/0.53  % (4323)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.36/0.53  % (4318)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.36/0.53  % (4327)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.36/0.53  % (4320)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.53  % SZS output start Proof for theBenchmark
% 1.36/0.53  fof(f412,plain,(
% 1.36/0.53    $false),
% 1.36/0.53    inference(trivial_inequality_removal,[],[f411])).
% 1.36/0.53  fof(f411,plain,(
% 1.36/0.53    k1_xboole_0 != k1_xboole_0),
% 1.36/0.53    inference(superposition,[],[f405,f62])).
% 1.36/0.53  fof(f62,plain,(
% 1.36/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.53    inference(cnf_transformation,[],[f3])).
% 1.36/0.53  fof(f3,axiom,(
% 1.36/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.36/0.53  fof(f405,plain,(
% 1.36/0.53    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,X0)) )),
% 1.36/0.53    inference(superposition,[],[f80,f394])).
% 1.36/0.53  fof(f394,plain,(
% 1.36/0.53    k1_xboole_0 = k1_tarski(sK7(sK6(sK3)))),
% 1.36/0.53    inference(subsumption_resolution,[],[f387,f333])).
% 1.36/0.53  fof(f333,plain,(
% 1.36/0.53    m1_subset_1(k1_tarski(sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.36/0.53    inference(subsumption_resolution,[],[f332,f194])).
% 1.36/0.53  fof(f194,plain,(
% 1.36/0.53    ~v1_xboole_0(u1_struct_0(sK3))),
% 1.36/0.53    inference(resolution,[],[f155,f110])).
% 1.36/0.53  fof(f110,plain,(
% 1.36/0.53    r2_hidden(sK7(sK6(sK3)),sK6(sK3))),
% 1.36/0.53    inference(resolution,[],[f101,f79])).
% 1.36/0.53  fof(f79,plain,(
% 1.36/0.53    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f53])).
% 1.36/0.53  fof(f53,plain,(
% 1.36/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).
% 1.36/0.53  fof(f52,plain,(
% 1.36/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f51,plain,(
% 1.36/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.53    inference(rectify,[],[f50])).
% 1.36/0.53  fof(f50,plain,(
% 1.36/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.53    inference(nnf_transformation,[],[f1])).
% 1.36/0.53  fof(f1,axiom,(
% 1.36/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.53  fof(f101,plain,(
% 1.36/0.53    ~v1_xboole_0(sK6(sK3))),
% 1.36/0.53    inference(subsumption_resolution,[],[f100,f54])).
% 1.36/0.53  fof(f54,plain,(
% 1.36/0.53    ~v2_struct_0(sK3)),
% 1.36/0.53    inference(cnf_transformation,[],[f39])).
% 1.36/0.53  fof(f39,plain,(
% 1.36/0.53    (v3_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f38,f37])).
% 1.36/0.53  fof(f37,plain,(
% 1.36/0.53    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f38,plain,(
% 1.36/0.53    ? [X1] : (v3_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) => (v3_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f18,plain,(
% 1.36/0.53    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.36/0.53    inference(flattening,[],[f17])).
% 1.36/0.53  fof(f17,plain,(
% 1.36/0.53    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f15])).
% 1.36/0.53  fof(f15,negated_conjecture,(
% 1.36/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.36/0.53    inference(negated_conjecture,[],[f14])).
% 1.36/0.53  fof(f14,conjecture,(
% 1.36/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 1.36/0.53  fof(f100,plain,(
% 1.36/0.53    ~v1_xboole_0(sK6(sK3)) | v2_struct_0(sK3)),
% 1.36/0.53    inference(subsumption_resolution,[],[f95,f55])).
% 1.36/0.53  fof(f55,plain,(
% 1.36/0.53    v2_pre_topc(sK3)),
% 1.36/0.53    inference(cnf_transformation,[],[f39])).
% 1.36/0.53  fof(f95,plain,(
% 1.36/0.53    ~v1_xboole_0(sK6(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.36/0.53    inference(resolution,[],[f56,f77])).
% 1.36/0.53  fof(f77,plain,(
% 1.36/0.53    ( ! [X0] : (~v1_xboole_0(sK6(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f49])).
% 1.36/0.53  fof(f49,plain,(
% 1.36/0.53    ! [X0] : ((~v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f48])).
% 1.36/0.53  fof(f48,plain,(
% 1.36/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f25,plain,(
% 1.36/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.36/0.53    inference(flattening,[],[f24])).
% 1.36/0.53  fof(f24,plain,(
% 1.36/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f16])).
% 1.36/0.53  fof(f16,plain,(
% 1.36/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.36/0.53    inference(pure_predicate_removal,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).
% 1.36/0.53  fof(f56,plain,(
% 1.36/0.53    l1_pre_topc(sK3)),
% 1.36/0.53    inference(cnf_transformation,[],[f39])).
% 1.36/0.53  fof(f155,plain,(
% 1.36/0.53    ( ! [X1] : (~r2_hidden(X1,sK6(sK3)) | ~v1_xboole_0(u1_struct_0(sK3))) )),
% 1.36/0.53    inference(resolution,[],[f99,f84])).
% 1.36/0.53  fof(f84,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f32])).
% 1.36/0.53  fof(f32,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f8])).
% 1.36/0.53  fof(f8,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.36/0.53  fof(f99,plain,(
% 1.36/0.53    m1_subset_1(sK6(sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.36/0.53    inference(subsumption_resolution,[],[f98,f54])).
% 1.36/0.53  fof(f98,plain,(
% 1.36/0.53    m1_subset_1(sK6(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3)),
% 1.36/0.53    inference(subsumption_resolution,[],[f94,f55])).
% 1.36/0.53  fof(f94,plain,(
% 1.36/0.53    m1_subset_1(sK6(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.36/0.53    inference(resolution,[],[f56,f76])).
% 1.36/0.53  fof(f76,plain,(
% 1.36/0.53    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f49])).
% 1.36/0.53  fof(f332,plain,(
% 1.36/0.53    m1_subset_1(k1_tarski(sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK3))),
% 1.36/0.53    inference(subsumption_resolution,[],[f329,f250])).
% 1.36/0.53  fof(f250,plain,(
% 1.36/0.53    m1_subset_1(sK7(sK6(sK3)),u1_struct_0(sK3))),
% 1.36/0.53    inference(resolution,[],[f156,f110])).
% 1.36/0.53  fof(f156,plain,(
% 1.36/0.53    ( ! [X2] : (~r2_hidden(X2,sK6(sK3)) | m1_subset_1(X2,u1_struct_0(sK3))) )),
% 1.36/0.53    inference(resolution,[],[f99,f83])).
% 1.36/0.53  fof(f83,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f31])).
% 1.36/0.53  fof(f31,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.36/0.53    inference(flattening,[],[f30])).
% 1.36/0.53  fof(f30,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.36/0.53    inference(ennf_transformation,[],[f7])).
% 1.36/0.53  fof(f7,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.36/0.53  fof(f329,plain,(
% 1.36/0.53    m1_subset_1(k1_tarski(sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK7(sK6(sK3)),u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 1.36/0.53    inference(superposition,[],[f260,f81])).
% 1.36/0.53  fof(f81,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f27])).
% 1.36/0.53  fof(f27,plain,(
% 1.36/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.36/0.53    inference(flattening,[],[f26])).
% 1.36/0.53  fof(f26,plain,(
% 1.36/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f11])).
% 1.36/0.53  fof(f11,axiom,(
% 1.36/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.36/0.53  fof(f260,plain,(
% 1.36/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.36/0.53    inference(subsumption_resolution,[],[f255,f194])).
% 1.36/0.53  fof(f255,plain,(
% 1.36/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK3))),
% 1.36/0.53    inference(resolution,[],[f250,f82])).
% 1.36/0.53  fof(f82,plain,(
% 1.36/0.53    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f29])).
% 1.36/0.53  fof(f29,plain,(
% 1.36/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.36/0.53    inference(flattening,[],[f28])).
% 1.36/0.53  % (4318)Refutation not found, incomplete strategy% (4318)------------------------------
% 1.36/0.53  % (4318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  fof(f28,plain,(
% 1.36/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f10])).
% 1.36/0.53  % (4318)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (4318)Memory used [KB]: 10618
% 1.36/0.53  % (4318)Time elapsed: 0.118 s
% 1.36/0.53  % (4318)------------------------------
% 1.36/0.53  % (4318)------------------------------
% 1.36/0.53  fof(f10,axiom,(
% 1.36/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.36/0.53  fof(f387,plain,(
% 1.36/0.53    k1_xboole_0 = k1_tarski(sK7(sK6(sK3))) | ~m1_subset_1(k1_tarski(sK7(sK6(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.36/0.53    inference(resolution,[],[f147,f272])).
% 1.36/0.53  fof(f272,plain,(
% 1.36/0.53    v2_tex_2(k1_tarski(sK7(sK6(sK3))),sK3)),
% 1.36/0.53    inference(subsumption_resolution,[],[f271,f194])).
% 1.36/0.53  fof(f271,plain,(
% 1.36/0.53    v2_tex_2(k1_tarski(sK7(sK6(sK3))),sK3) | v1_xboole_0(u1_struct_0(sK3))),
% 1.36/0.53    inference(subsumption_resolution,[],[f270,f250])).
% 1.36/0.53  fof(f270,plain,(
% 1.36/0.53    v2_tex_2(k1_tarski(sK7(sK6(sK3))),sK3) | ~m1_subset_1(sK7(sK6(sK3)),u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 1.36/0.53    inference(superposition,[],[f253,f81])).
% 1.36/0.53  fof(f253,plain,(
% 1.36/0.53    v2_tex_2(k6_domain_1(u1_struct_0(sK3),sK7(sK6(sK3))),sK3)),
% 1.36/0.53    inference(resolution,[],[f250,f103])).
% 1.36/0.53  fof(f103,plain,(
% 1.36/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f102,f54])).
% 1.36/0.53  fof(f102,plain,(
% 1.36/0.53    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK3)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f96,f55])).
% 1.36/0.53  fof(f96,plain,(
% 1.36/0.53    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.36/0.53    inference(resolution,[],[f56,f75])).
% 1.36/0.53  fof(f75,plain,(
% 1.36/0.53    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f23])).
% 1.36/0.53  fof(f23,plain,(
% 1.36/0.53    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.36/0.53    inference(flattening,[],[f22])).
% 1.36/0.53  fof(f22,plain,(
% 1.36/0.53    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f13])).
% 1.36/0.53  fof(f13,axiom,(
% 1.36/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 1.36/0.53  fof(f147,plain,(
% 1.36/0.53    ( ! [X0] : (~v2_tex_2(X0,sK3) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f144,f60])).
% 1.36/0.53  fof(f60,plain,(
% 1.36/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f4])).
% 1.36/0.53  fof(f4,axiom,(
% 1.36/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.36/0.53  fof(f144,plain,(
% 1.36/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 1.36/0.53    inference(resolution,[],[f137,f68])).
% 1.36/0.53  fof(f68,plain,(
% 1.36/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f47])).
% 1.36/0.53  fof(f47,plain,(
% 1.36/0.53    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 1.36/0.53  fof(f46,plain,(
% 1.36/0.53    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f45,plain,(
% 1.36/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.36/0.53    inference(rectify,[],[f44])).
% 1.36/0.53  fof(f44,plain,(
% 1.36/0.53    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 1.36/0.53    inference(nnf_transformation,[],[f33])).
% 1.36/0.53  fof(f33,plain,(
% 1.36/0.53    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.36/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.53  fof(f137,plain,(
% 1.36/0.53    sP0(k1_xboole_0,sK3)),
% 1.36/0.53    inference(resolution,[],[f135,f66])).
% 1.36/0.53  fof(f66,plain,(
% 1.36/0.53    ( ! [X0,X1] : (sP0(X1,X0) | ~sP1(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f43])).
% 1.36/0.53  fof(f43,plain,(
% 1.36/0.53    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 1.36/0.53    inference(flattening,[],[f42])).
% 1.36/0.53  fof(f42,plain,(
% 1.36/0.53    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 1.36/0.53    inference(nnf_transformation,[],[f34])).
% 1.36/0.53  fof(f34,plain,(
% 1.36/0.53    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 1.36/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.36/0.53  fof(f135,plain,(
% 1.36/0.53    sP1(sK3,k1_xboole_0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f132,f121])).
% 1.36/0.53  fof(f121,plain,(
% 1.36/0.53    v3_tex_2(k1_xboole_0,sK3)),
% 1.36/0.53    inference(backward_demodulation,[],[f59,f106])).
% 1.36/0.53  fof(f106,plain,(
% 1.36/0.53    k1_xboole_0 = sK4),
% 1.36/0.53    inference(resolution,[],[f57,f74])).
% 1.36/0.53  fof(f74,plain,(
% 1.36/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f21])).
% 1.36/0.53  fof(f21,plain,(
% 1.36/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.36/0.54  fof(f57,plain,(
% 1.36/0.54    v1_xboole_0(sK4)),
% 1.36/0.54    inference(cnf_transformation,[],[f39])).
% 1.36/0.54  fof(f59,plain,(
% 1.36/0.54    v3_tex_2(sK4,sK3)),
% 1.36/0.54    inference(cnf_transformation,[],[f39])).
% 1.36/0.54  fof(f132,plain,(
% 1.36/0.54    sP1(sK3,k1_xboole_0) | ~v3_tex_2(k1_xboole_0,sK3)),
% 1.36/0.54    inference(resolution,[],[f129,f63])).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    ( ! [X0,X1] : (sP1(X1,X0) | ~v3_tex_2(X0,X1) | ~sP2(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f41])).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 1.36/0.54    inference(rectify,[],[f40])).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 1.36/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.36/0.54  fof(f129,plain,(
% 1.36/0.54    sP2(k1_xboole_0,sK3)),
% 1.36/0.54    inference(forward_demodulation,[],[f117,f106])).
% 1.36/0.54  fof(f117,plain,(
% 1.36/0.54    sP2(sK4,sK3)),
% 1.36/0.54    inference(subsumption_resolution,[],[f111,f56])).
% 1.36/0.54  fof(f111,plain,(
% 1.36/0.54    sP2(sK4,sK3) | ~l1_pre_topc(sK3)),
% 1.36/0.54    inference(resolution,[],[f58,f73])).
% 1.36/0.54  fof(f73,plain,(
% 1.36/0.54    ( ! [X0,X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(definition_folding,[],[f20,f35,f34,f33])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.36/0.54    inference(cnf_transformation,[],[f39])).
% 1.36/0.54  fof(f80,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (4320)------------------------------
% 1.36/0.54  % (4320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (4320)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (4320)Memory used [KB]: 1791
% 1.36/0.54  % (4320)Time elapsed: 0.095 s
% 1.36/0.54  % (4320)------------------------------
% 1.36/0.54  % (4320)------------------------------
% 1.36/0.54  % (4313)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (4311)Success in time 0.169 s
%------------------------------------------------------------------------------
