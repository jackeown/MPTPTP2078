%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:50 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 157 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   21
%              Number of atoms          :  306 ( 676 expanded)
%              Number of equality atoms :   46 (  54 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(subsumption_resolution,[],[f184,f51])).

fof(f51,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( v3_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f39,f38])).

% (21894)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( v3_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_xboole_0(X1) )
   => ( v3_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f184,plain,(
    ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f183,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f183,plain,(
    ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f182,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f182,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f181,f55])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f181,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f71,f145])).

fof(f145,plain,(
    k1_xboole_0 = u1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f144,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f144,plain,
    ( k1_xboole_0 = u1_struct_0(sK2)
    | ~ r2_hidden(sK5(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f142,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f142,plain,
    ( ~ m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = u1_struct_0(sK2)
    | ~ r2_hidden(sK5(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f124,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f124,plain,
    ( ~ m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f121,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f73,f58])).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f73,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f121,plain,
    ( ~ m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = k1_tarski(sK5(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(resolution,[],[f119,f109])).

fof(f109,plain,
    ( v2_tex_2(k1_tarski(sK5(u1_struct_0(sK2))),sK2)
    | ~ m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(superposition,[],[f108,f101])).

fof(f101,plain,(
    ! [X0] :
      ( k1_tarski(sK5(X0)) = k6_domain_1(X0,sK5(X0))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f100,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

% (21891)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f100,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k1_tarski(sK5(X0)) = k6_domain_1(X0,sK5(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f96,f72])).

fof(f96,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,X3)
      | v1_xboole_0(X3)
      | k6_domain_1(X3,X4) = k1_tarski(X4) ) ),
    inference(resolution,[],[f76,f74])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f108,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f106,f51])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f119,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f118,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,(
    sP0(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f88,f82])).

fof(f82,plain,(
    v3_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f54,f78])).

fof(f78,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,
    ( ~ v3_tex_2(k1_xboole_0,sK2)
    | sP0(k1_xboole_0,sK2) ),
    inference(resolution,[],[f85,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f85,plain,(
    sP1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f68,f51])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK4(X0,X1) != X0
          & r1_tarski(X0,sK4(X0,X1))
          & v2_tex_2(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) != X0
        & r1_tarski(X0,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n016.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 13:22:04 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.13/0.36  % (21888)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.13/0.36  % (21890)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.13/0.36  % (21880)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.13/0.36  % (21881)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.13/0.36  % (21889)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.13/0.37  % (21883)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.13/0.37  % (21885)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.13/0.37  % (21883)Refutation not found, incomplete strategy% (21883)------------------------------
% 0.13/0.37  % (21883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.37  % (21882)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.13/0.37  % (21887)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.13/0.37  % (21890)Refutation not found, incomplete strategy% (21890)------------------------------
% 0.13/0.37  % (21890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.37  % (21890)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.37  
% 0.13/0.37  % (21890)Memory used [KB]: 6140
% 0.13/0.37  % (21890)Time elapsed: 0.066 s
% 0.13/0.37  % (21890)------------------------------
% 0.13/0.37  % (21890)------------------------------
% 0.13/0.37  % (21900)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.13/0.37  % (21882)Refutation not found, incomplete strategy% (21882)------------------------------
% 0.13/0.37  % (21882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.37  % (21882)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.37  
% 0.13/0.37  % (21882)Memory used [KB]: 6140
% 0.13/0.37  % (21882)Time elapsed: 0.065 s
% 0.13/0.37  % (21882)------------------------------
% 0.13/0.37  % (21882)------------------------------
% 0.13/0.37  % (21899)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.13/0.38  % (21888)Refutation not found, incomplete strategy% (21888)------------------------------
% 0.13/0.38  % (21888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.38  % (21888)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.38  
% 0.13/0.38  % (21888)Memory used [KB]: 10746
% 0.13/0.38  % (21888)Time elapsed: 0.068 s
% 0.13/0.38  % (21888)------------------------------
% 0.13/0.38  % (21888)------------------------------
% 0.13/0.38  % (21898)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.13/0.38  % (21893)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.13/0.38  % (21880)Refutation found. Thanks to Tanya!
% 0.13/0.38  % SZS status Theorem for theBenchmark
% 0.13/0.38  % SZS output start Proof for theBenchmark
% 0.13/0.38  fof(f185,plain,(
% 0.13/0.38    $false),
% 0.13/0.38    inference(subsumption_resolution,[],[f184,f51])).
% 0.13/0.38  fof(f51,plain,(
% 0.13/0.38    l1_pre_topc(sK2)),
% 0.13/0.38    inference(cnf_transformation,[],[f40])).
% 0.13/0.38  fof(f40,plain,(
% 0.13/0.38    (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.13/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f39,f38])).
% 0.13/0.38  % (21894)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.13/0.38  fof(f38,plain,(
% 0.13/0.38    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.13/0.38    introduced(choice_axiom,[])).
% 0.13/0.38  fof(f39,plain,(
% 0.13/0.38    ? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 0.13/0.38    introduced(choice_axiom,[])).
% 0.13/0.38  fof(f19,plain,(
% 0.13/0.38    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.13/0.38    inference(flattening,[],[f18])).
% 0.13/0.38  fof(f18,plain,(
% 0.13/0.38    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.13/0.38    inference(ennf_transformation,[],[f17])).
% 0.13/0.38  fof(f17,negated_conjecture,(
% 0.13/0.38    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.13/0.38    inference(negated_conjecture,[],[f16])).
% 0.13/0.38  fof(f16,conjecture,(
% 0.13/0.38    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.13/0.38  fof(f184,plain,(
% 0.13/0.38    ~l1_pre_topc(sK2)),
% 0.13/0.38    inference(resolution,[],[f183,f59])).
% 0.13/0.38  fof(f59,plain,(
% 0.13/0.38    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f20])).
% 0.13/0.38  fof(f20,plain,(
% 0.13/0.38    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.13/0.38    inference(ennf_transformation,[],[f11])).
% 0.13/0.38  fof(f11,axiom,(
% 0.13/0.38    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.13/0.38  fof(f183,plain,(
% 0.13/0.38    ~l1_struct_0(sK2)),
% 0.13/0.38    inference(subsumption_resolution,[],[f182,f49])).
% 0.13/0.38  fof(f49,plain,(
% 0.13/0.38    ~v2_struct_0(sK2)),
% 0.13/0.38    inference(cnf_transformation,[],[f40])).
% 0.13/0.38  fof(f182,plain,(
% 0.13/0.38    ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.13/0.38    inference(subsumption_resolution,[],[f181,f55])).
% 0.13/0.38  fof(f55,plain,(
% 0.13/0.38    v1_xboole_0(k1_xboole_0)),
% 0.13/0.38    inference(cnf_transformation,[],[f1])).
% 0.13/0.38  fof(f1,axiom,(
% 0.13/0.38    v1_xboole_0(k1_xboole_0)),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.13/0.38  fof(f181,plain,(
% 0.13/0.38    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.13/0.38    inference(superposition,[],[f71,f145])).
% 0.13/0.38  fof(f145,plain,(
% 0.13/0.38    k1_xboole_0 = u1_struct_0(sK2)),
% 0.13/0.38    inference(subsumption_resolution,[],[f144,f72])).
% 0.13/0.38  fof(f72,plain,(
% 0.13/0.38    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.13/0.38    inference(cnf_transformation,[],[f48])).
% 0.13/0.38  fof(f48,plain,(
% 0.13/0.38    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 0.13/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f47])).
% 0.13/0.38  fof(f47,plain,(
% 0.13/0.38    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.13/0.38    introduced(choice_axiom,[])).
% 0.13/0.38  fof(f28,plain,(
% 0.13/0.38    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.13/0.38    inference(ennf_transformation,[],[f3])).
% 0.13/0.38  fof(f3,axiom,(
% 0.13/0.38    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.13/0.38  fof(f144,plain,(
% 0.13/0.38    k1_xboole_0 = u1_struct_0(sK2) | ~r2_hidden(sK5(u1_struct_0(sK2)),u1_struct_0(sK2))),
% 0.13/0.38    inference(subsumption_resolution,[],[f142,f75])).
% 0.13/0.38  fof(f75,plain,(
% 0.13/0.38    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f30])).
% 0.13/0.38  fof(f30,plain,(
% 0.13/0.38    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.13/0.38    inference(ennf_transformation,[],[f8])).
% 0.13/0.38  fof(f8,axiom,(
% 0.13/0.38    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.13/0.38  fof(f142,plain,(
% 0.13/0.38    ~m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = u1_struct_0(sK2) | ~r2_hidden(sK5(u1_struct_0(sK2)),u1_struct_0(sK2))),
% 0.13/0.38    inference(resolution,[],[f124,f74])).
% 0.13/0.38  fof(f74,plain,(
% 0.13/0.38    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f29])).
% 0.13/0.38  fof(f29,plain,(
% 0.13/0.38    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.13/0.38    inference(ennf_transformation,[],[f9])).
% 0.13/0.38  fof(f9,axiom,(
% 0.13/0.38    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.13/0.38  fof(f124,plain,(
% 0.13/0.38    ~m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2)) | ~m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = u1_struct_0(sK2)),
% 0.13/0.38    inference(subsumption_resolution,[],[f121,f83])).
% 0.13/0.38  fof(f83,plain,(
% 0.13/0.38    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.13/0.38    inference(superposition,[],[f73,f58])).
% 0.13/0.38  fof(f58,plain,(
% 0.13/0.38    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.13/0.38    inference(cnf_transformation,[],[f4])).
% 0.13/0.38  fof(f4,axiom,(
% 0.13/0.38    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.13/0.38  fof(f73,plain,(
% 0.13/0.38    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f6])).
% 0.13/0.38  fof(f6,axiom,(
% 0.13/0.38    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.13/0.38  fof(f121,plain,(
% 0.13/0.38    ~m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = k1_tarski(sK5(u1_struct_0(sK2))) | ~m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2)) | k1_xboole_0 = u1_struct_0(sK2)),
% 0.13/0.38    inference(resolution,[],[f119,f109])).
% 0.13/0.38  fof(f109,plain,(
% 0.13/0.38    v2_tex_2(k1_tarski(sK5(u1_struct_0(sK2))),sK2) | ~m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2)) | k1_xboole_0 = u1_struct_0(sK2)),
% 0.13/0.38    inference(superposition,[],[f108,f101])).
% 0.13/0.38  fof(f101,plain,(
% 0.13/0.38    ( ! [X0] : (k1_tarski(sK5(X0)) = k6_domain_1(X0,sK5(X0)) | k1_xboole_0 = X0) )),
% 0.13/0.38    inference(subsumption_resolution,[],[f100,f69])).
% 0.13/0.38  fof(f69,plain,(
% 0.13/0.38    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.13/0.38    inference(cnf_transformation,[],[f23])).
% 0.13/0.38  fof(f23,plain,(
% 0.13/0.38    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.13/0.38    inference(ennf_transformation,[],[f2])).
% 0.13/0.38  fof(f2,axiom,(
% 0.13/0.38    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.13/0.38  % (21891)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.13/0.38  fof(f100,plain,(
% 0.13/0.38    ( ! [X0] : (v1_xboole_0(X0) | k1_tarski(sK5(X0)) = k6_domain_1(X0,sK5(X0)) | k1_xboole_0 = X0) )),
% 0.13/0.38    inference(resolution,[],[f96,f72])).
% 0.13/0.38  fof(f96,plain,(
% 0.13/0.38    ( ! [X4,X3] : (~r2_hidden(X4,X3) | v1_xboole_0(X3) | k6_domain_1(X3,X4) = k1_tarski(X4)) )),
% 0.13/0.38    inference(resolution,[],[f76,f74])).
% 0.13/0.38  fof(f76,plain,(
% 0.13/0.38    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f32])).
% 0.13/0.38  fof(f32,plain,(
% 0.13/0.38    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.13/0.38    inference(flattening,[],[f31])).
% 0.13/0.38  fof(f31,plain,(
% 0.13/0.38    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.13/0.38    inference(ennf_transformation,[],[f13])).
% 0.13/0.38  fof(f13,axiom,(
% 0.13/0.38    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.13/0.38  fof(f108,plain,(
% 0.13/0.38    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 0.13/0.38    inference(subsumption_resolution,[],[f107,f49])).
% 0.13/0.38  fof(f107,plain,(
% 0.13/0.38    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) | v2_struct_0(sK2)) )),
% 0.13/0.38    inference(subsumption_resolution,[],[f106,f51])).
% 0.13/0.38  fof(f106,plain,(
% 0.13/0.38    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) | v2_struct_0(sK2)) )),
% 0.13/0.38    inference(resolution,[],[f70,f50])).
% 0.13/0.38  fof(f50,plain,(
% 0.13/0.38    v2_pre_topc(sK2)),
% 0.13/0.38    inference(cnf_transformation,[],[f40])).
% 0.13/0.38  fof(f70,plain,(
% 0.13/0.38    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | v2_struct_0(X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f25])).
% 0.13/0.38  fof(f25,plain,(
% 0.13/0.38    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.13/0.38    inference(flattening,[],[f24])).
% 0.13/0.38  fof(f24,plain,(
% 0.13/0.38    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.13/0.38    inference(ennf_transformation,[],[f15])).
% 0.13/0.38  fof(f15,axiom,(
% 0.13/0.38    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.13/0.38  fof(f119,plain,(
% 0.13/0.38    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = X0) )),
% 0.13/0.38    inference(subsumption_resolution,[],[f118,f56])).
% 0.13/0.38  fof(f56,plain,(
% 0.13/0.38    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f5])).
% 0.13/0.38  fof(f5,axiom,(
% 0.13/0.38    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.13/0.38  fof(f118,plain,(
% 0.13/0.38    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = X0) )),
% 0.13/0.38    inference(resolution,[],[f63,f89])).
% 0.13/0.38  fof(f89,plain,(
% 0.13/0.38    sP0(k1_xboole_0,sK2)),
% 0.13/0.38    inference(subsumption_resolution,[],[f88,f82])).
% 0.13/0.38  fof(f82,plain,(
% 0.13/0.38    v3_tex_2(k1_xboole_0,sK2)),
% 0.13/0.38    inference(backward_demodulation,[],[f54,f78])).
% 0.13/0.38  fof(f78,plain,(
% 0.13/0.38    k1_xboole_0 = sK3),
% 0.13/0.38    inference(resolution,[],[f69,f52])).
% 0.13/0.38  fof(f52,plain,(
% 0.13/0.38    v1_xboole_0(sK3)),
% 0.13/0.38    inference(cnf_transformation,[],[f40])).
% 0.13/0.38  fof(f54,plain,(
% 0.13/0.38    v3_tex_2(sK3,sK2)),
% 0.13/0.38    inference(cnf_transformation,[],[f40])).
% 0.13/0.38  fof(f88,plain,(
% 0.13/0.38    ~v3_tex_2(k1_xboole_0,sK2) | sP0(k1_xboole_0,sK2)),
% 0.13/0.38    inference(resolution,[],[f85,f60])).
% 0.13/0.38  fof(f60,plain,(
% 0.13/0.38    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f41])).
% 0.13/0.38  fof(f41,plain,(
% 0.13/0.38    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.13/0.38    inference(nnf_transformation,[],[f36])).
% 0.13/0.38  fof(f36,plain,(
% 0.13/0.38    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.13/0.38    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.13/0.38  fof(f85,plain,(
% 0.13/0.38    sP1(sK2,k1_xboole_0)),
% 0.13/0.38    inference(resolution,[],[f84,f57])).
% 0.13/0.38  fof(f57,plain,(
% 0.13/0.38    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.13/0.38    inference(cnf_transformation,[],[f7])).
% 0.13/0.38  fof(f7,axiom,(
% 0.13/0.38    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.13/0.38  fof(f84,plain,(
% 0.13/0.38    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.13/0.38    inference(resolution,[],[f68,f51])).
% 0.13/0.38  fof(f68,plain,(
% 0.13/0.38    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f37])).
% 0.13/0.38  fof(f37,plain,(
% 0.13/0.38    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.13/0.38    inference(definition_folding,[],[f22,f36,f35])).
% 0.13/0.38  fof(f35,plain,(
% 0.13/0.38    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 0.13/0.38    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.13/0.38  fof(f22,plain,(
% 0.13/0.38    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.13/0.38    inference(flattening,[],[f21])).
% 0.13/0.38  fof(f21,plain,(
% 0.13/0.38    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.13/0.38    inference(ennf_transformation,[],[f14])).
% 0.13/0.38  fof(f14,axiom,(
% 0.13/0.38    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.13/0.38  fof(f63,plain,(
% 0.13/0.38    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | X0 = X3) )),
% 0.13/0.38    inference(cnf_transformation,[],[f46])).
% 0.13/0.38  fof(f46,plain,(
% 0.13/0.38    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.13/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 0.13/0.38  fof(f45,plain,(
% 0.13/0.38    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.13/0.38    introduced(choice_axiom,[])).
% 0.13/0.38  fof(f44,plain,(
% 0.13/0.38    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.13/0.38    inference(rectify,[],[f43])).
% 0.13/0.38  fof(f43,plain,(
% 0.13/0.38    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.13/0.38    inference(flattening,[],[f42])).
% 0.13/0.38  fof(f42,plain,(
% 0.13/0.38    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.13/0.38    inference(nnf_transformation,[],[f35])).
% 0.13/0.38  fof(f71,plain,(
% 0.13/0.38    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f27])).
% 0.13/0.38  fof(f27,plain,(
% 0.13/0.38    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.13/0.38    inference(flattening,[],[f26])).
% 0.13/0.38  fof(f26,plain,(
% 0.13/0.38    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.13/0.38    inference(ennf_transformation,[],[f12])).
% 0.13/0.38  fof(f12,axiom,(
% 0.13/0.38    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.13/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.13/0.38  % SZS output end Proof for theBenchmark
% 0.13/0.38  % (21880)------------------------------
% 0.13/0.38  % (21880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.38  % (21880)Termination reason: Refutation
% 0.13/0.38  
% 0.13/0.38  % (21880)Memory used [KB]: 6268
% 0.13/0.38  % (21880)Time elapsed: 0.077 s
% 0.13/0.38  % (21880)------------------------------
% 0.13/0.38  % (21880)------------------------------
% 0.13/0.38  % (21886)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.13/0.38  % (21876)Success in time 0.105 s
%------------------------------------------------------------------------------
