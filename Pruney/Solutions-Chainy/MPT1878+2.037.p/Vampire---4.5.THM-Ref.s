%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:48 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 210 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  294 ( 911 expanded)
%              Number of equality atoms :   36 (  46 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(subsumption_resolution,[],[f151,f47])).

% (24442)Refutation not found, incomplete strategy% (24442)------------------------------
% (24442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24442)Termination reason: Refutation not found, incomplete strategy

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

% (24442)Memory used [KB]: 10618
% (24442)Time elapsed: 0.102 s
% (24442)------------------------------
% (24442)------------------------------
fof(f36,plain,
    ( v3_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
    ( ? [X1] :
        ( v3_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_xboole_0(X1) )
   => ( v3_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v1_xboole_0(sK3) ) ),
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

fof(f151,plain,(
    ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f136,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f136,plain,(
    ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f134,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f134,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f132,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f132,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f122,f131])).

fof(f131,plain,(
    ~ m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f128,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f68,f53])).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f128,plain,
    ( ~ m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = k1_tarski(sK5(u1_struct_0(sK2))) ),
    inference(resolution,[],[f126,f121])).

fof(f121,plain,(
    v2_tex_2(k1_tarski(sK5(u1_struct_0(sK2))),sK2) ),
    inference(subsumption_resolution,[],[f119,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f5,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f119,plain,
    ( v2_tex_2(k1_tarski(sK5(u1_struct_0(sK2))),sK2)
    | ~ m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(superposition,[],[f109,f114])).

fof(f114,plain,(
    k1_tarski(sK5(u1_struct_0(sK2))) = k6_domain_1(u1_struct_0(sK2),sK5(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f113,f47])).

fof(f113,plain,
    ( k1_tarski(sK5(u1_struct_0(sK2))) = k6_domain_1(u1_struct_0(sK2),sK5(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f112,f54])).

fof(f112,plain,
    ( ~ l1_struct_0(sK2)
    | k1_tarski(sK5(u1_struct_0(sK2))) = k6_domain_1(u1_struct_0(sK2),sK5(u1_struct_0(sK2))) ),
    inference(resolution,[],[f88,f45])).

fof(f88,plain,(
    ! [X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | k6_domain_1(u1_struct_0(X1),sK5(u1_struct_0(X1))) = k1_tarski(sK5(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f85,f66])).

fof(f85,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | k6_domain_1(X1,sK5(X1)) = k1_tarski(sK5(X1)) ) ),
    inference(resolution,[],[f69,f67])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f109,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f107,f47])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f126,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f125,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f81])).

fof(f81,plain,(
    sP0(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f80,f74])).

fof(f74,plain,(
    v3_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f50,f71])).

fof(f71,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f50,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,
    ( ~ v3_tex_2(k1_xboole_0,sK2)
    | sP0(k1_xboole_0,sK2) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f78,plain,(
    sP1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f77,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(flattening,[],[f20])).

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
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f122,plain,
    ( m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f120,f67])).

fof(f120,plain,
    ( m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(superposition,[],[f70,f114])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (24445)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (24443)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (24448)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (24453)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (24447)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (24462)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (24447)Refutation not found, incomplete strategy% (24447)------------------------------
% 0.20/0.51  % (24447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24447)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24447)Memory used [KB]: 6140
% 0.20/0.51  % (24447)Time elapsed: 0.096 s
% 0.20/0.51  % (24447)------------------------------
% 0.20/0.51  % (24447)------------------------------
% 0.20/0.51  % (24448)Refutation not found, incomplete strategy% (24448)------------------------------
% 0.20/0.51  % (24448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (24456)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.17/0.51  % (24465)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.17/0.51  % (24448)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.51  
% 1.17/0.51  % (24448)Memory used [KB]: 10618
% 1.17/0.51  % (24448)Time elapsed: 0.096 s
% 1.17/0.51  % (24448)------------------------------
% 1.17/0.51  % (24448)------------------------------
% 1.17/0.51  % (24459)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.17/0.51  % (24444)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.17/0.52  % (24463)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.17/0.52  % (24446)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.17/0.52  % (24442)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.17/0.52  % (24451)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.17/0.52  % (24445)Refutation found. Thanks to Tanya!
% 1.17/0.52  % SZS status Theorem for theBenchmark
% 1.17/0.52  % SZS output start Proof for theBenchmark
% 1.17/0.52  fof(f152,plain,(
% 1.17/0.52    $false),
% 1.17/0.52    inference(subsumption_resolution,[],[f151,f47])).
% 1.17/0.52  % (24442)Refutation not found, incomplete strategy% (24442)------------------------------
% 1.17/0.52  % (24442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (24442)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.52  
% 1.17/0.52  fof(f47,plain,(
% 1.17/0.52    l1_pre_topc(sK2)),
% 1.17/0.52    inference(cnf_transformation,[],[f36])).
% 1.17/0.52  % (24442)Memory used [KB]: 10618
% 1.17/0.52  % (24442)Time elapsed: 0.102 s
% 1.17/0.52  % (24442)------------------------------
% 1.17/0.52  % (24442)------------------------------
% 1.17/0.52  fof(f36,plain,(
% 1.17/0.52    (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.17/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f35,f34])).
% 1.17/0.52  fof(f34,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    ? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f18,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/0.52    inference(flattening,[],[f17])).
% 1.17/0.52  fof(f17,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f15])).
% 1.17/0.52  fof(f15,negated_conjecture,(
% 1.17/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.17/0.52    inference(negated_conjecture,[],[f14])).
% 1.17/0.52  fof(f14,conjecture,(
% 1.17/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 1.17/0.52  fof(f151,plain,(
% 1.17/0.52    ~l1_pre_topc(sK2)),
% 1.17/0.52    inference(resolution,[],[f136,f54])).
% 1.17/0.52  fof(f54,plain,(
% 1.17/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f19])).
% 1.17/0.52  fof(f19,plain,(
% 1.17/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f8])).
% 1.17/0.52  fof(f8,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.17/0.52  fof(f136,plain,(
% 1.17/0.52    ~l1_struct_0(sK2)),
% 1.17/0.52    inference(subsumption_resolution,[],[f134,f45])).
% 1.17/0.52  fof(f45,plain,(
% 1.17/0.52    ~v2_struct_0(sK2)),
% 1.17/0.52    inference(cnf_transformation,[],[f36])).
% 1.17/0.52  fof(f134,plain,(
% 1.17/0.52    ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 1.17/0.52    inference(resolution,[],[f132,f66])).
% 1.17/0.52  fof(f66,plain,(
% 1.17/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f26])).
% 1.17/0.52  fof(f26,plain,(
% 1.17/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.17/0.52    inference(flattening,[],[f25])).
% 1.17/0.52  fof(f25,plain,(
% 1.17/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f9])).
% 1.17/0.52  fof(f9,axiom,(
% 1.17/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.17/0.52  fof(f132,plain,(
% 1.17/0.52    v1_xboole_0(u1_struct_0(sK2))),
% 1.17/0.52    inference(subsumption_resolution,[],[f122,f131])).
% 1.17/0.52  fof(f131,plain,(
% 1.17/0.52    ~m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.17/0.52    inference(subsumption_resolution,[],[f128,f76])).
% 1.17/0.52  fof(f76,plain,(
% 1.17/0.52    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 1.17/0.52    inference(superposition,[],[f68,f53])).
% 1.17/0.52  fof(f53,plain,(
% 1.17/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f2])).
% 1.17/0.52  fof(f2,axiom,(
% 1.17/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.17/0.52  fof(f68,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f4])).
% 1.17/0.52  fof(f4,axiom,(
% 1.17/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.17/0.52  fof(f128,plain,(
% 1.17/0.52    ~m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = k1_tarski(sK5(u1_struct_0(sK2)))),
% 1.17/0.52    inference(resolution,[],[f126,f121])).
% 1.17/0.52  fof(f121,plain,(
% 1.17/0.52    v2_tex_2(k1_tarski(sK5(u1_struct_0(sK2))),sK2)),
% 1.17/0.52    inference(subsumption_resolution,[],[f119,f67])).
% 1.17/0.52  fof(f67,plain,(
% 1.17/0.52    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f44])).
% 1.17/0.52  fof(f44,plain,(
% 1.17/0.52    ! [X0] : m1_subset_1(sK5(X0),X0)),
% 1.17/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f5,f43])).
% 1.17/0.52  fof(f43,plain,(
% 1.17/0.52    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK5(X0),X0))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f5,axiom,(
% 1.17/0.52    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.17/0.52  fof(f119,plain,(
% 1.17/0.52    v2_tex_2(k1_tarski(sK5(u1_struct_0(sK2))),sK2) | ~m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2))),
% 1.17/0.52    inference(superposition,[],[f109,f114])).
% 1.17/0.52  fof(f114,plain,(
% 1.17/0.52    k1_tarski(sK5(u1_struct_0(sK2))) = k6_domain_1(u1_struct_0(sK2),sK5(u1_struct_0(sK2)))),
% 1.17/0.52    inference(subsumption_resolution,[],[f113,f47])).
% 1.17/0.52  fof(f113,plain,(
% 1.17/0.52    k1_tarski(sK5(u1_struct_0(sK2))) = k6_domain_1(u1_struct_0(sK2),sK5(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.17/0.52    inference(resolution,[],[f112,f54])).
% 1.17/0.52  fof(f112,plain,(
% 1.17/0.52    ~l1_struct_0(sK2) | k1_tarski(sK5(u1_struct_0(sK2))) = k6_domain_1(u1_struct_0(sK2),sK5(u1_struct_0(sK2)))),
% 1.17/0.52    inference(resolution,[],[f88,f45])).
% 1.17/0.52  fof(f88,plain,(
% 1.17/0.52    ( ! [X1] : (v2_struct_0(X1) | ~l1_struct_0(X1) | k6_domain_1(u1_struct_0(X1),sK5(u1_struct_0(X1))) = k1_tarski(sK5(u1_struct_0(X1)))) )),
% 1.17/0.52    inference(resolution,[],[f85,f66])).
% 1.17/0.52  fof(f85,plain,(
% 1.17/0.52    ( ! [X1] : (v1_xboole_0(X1) | k6_domain_1(X1,sK5(X1)) = k1_tarski(sK5(X1))) )),
% 1.17/0.52    inference(resolution,[],[f69,f67])).
% 1.17/0.52  fof(f69,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f28])).
% 1.17/0.52  fof(f28,plain,(
% 1.17/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.17/0.52    inference(flattening,[],[f27])).
% 1.17/0.52  fof(f27,plain,(
% 1.17/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f11])).
% 1.17/0.52  fof(f11,axiom,(
% 1.17/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.17/0.52  fof(f109,plain,(
% 1.17/0.52    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f108,f45])).
% 1.17/0.52  fof(f108,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) | v2_struct_0(sK2)) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f107,f47])).
% 1.17/0.52  fof(f107,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) | v2_struct_0(sK2)) )),
% 1.17/0.52    inference(resolution,[],[f65,f46])).
% 1.17/0.52  fof(f46,plain,(
% 1.17/0.52    v2_pre_topc(sK2)),
% 1.17/0.52    inference(cnf_transformation,[],[f36])).
% 1.17/0.52  fof(f65,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | v2_struct_0(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f24])).
% 1.17/0.52  fof(f24,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.52    inference(flattening,[],[f23])).
% 1.17/0.52  fof(f23,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f13])).
% 1.17/0.52  fof(f13,axiom,(
% 1.17/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 1.17/0.52  fof(f126,plain,(
% 1.17/0.52    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f125,f51])).
% 1.17/0.52  fof(f51,plain,(
% 1.17/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f3])).
% 1.17/0.52  fof(f3,axiom,(
% 1.17/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.17/0.52  fof(f125,plain,(
% 1.17/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(resolution,[],[f58,f81])).
% 1.17/0.52  fof(f81,plain,(
% 1.17/0.52    sP0(k1_xboole_0,sK2)),
% 1.17/0.52    inference(subsumption_resolution,[],[f80,f74])).
% 1.17/0.52  fof(f74,plain,(
% 1.17/0.52    v3_tex_2(k1_xboole_0,sK2)),
% 1.17/0.52    inference(backward_demodulation,[],[f50,f71])).
% 1.17/0.52  fof(f71,plain,(
% 1.17/0.52    k1_xboole_0 = sK3),
% 1.17/0.52    inference(resolution,[],[f64,f48])).
% 1.17/0.52  fof(f48,plain,(
% 1.17/0.52    v1_xboole_0(sK3)),
% 1.17/0.52    inference(cnf_transformation,[],[f36])).
% 1.17/0.52  fof(f64,plain,(
% 1.17/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f22])).
% 1.17/0.52  fof(f22,plain,(
% 1.17/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f1])).
% 1.17/0.52  fof(f1,axiom,(
% 1.17/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.17/0.52  fof(f50,plain,(
% 1.17/0.52    v3_tex_2(sK3,sK2)),
% 1.17/0.52    inference(cnf_transformation,[],[f36])).
% 1.17/0.52  fof(f80,plain,(
% 1.17/0.52    ~v3_tex_2(k1_xboole_0,sK2) | sP0(k1_xboole_0,sK2)),
% 1.17/0.52    inference(resolution,[],[f78,f55])).
% 1.17/0.52  fof(f55,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f37])).
% 1.17/0.52  fof(f37,plain,(
% 1.17/0.52    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.17/0.52    inference(nnf_transformation,[],[f32])).
% 1.17/0.52  fof(f32,plain,(
% 1.17/0.52    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.17/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.17/0.52  fof(f78,plain,(
% 1.17/0.52    sP1(sK2,k1_xboole_0)),
% 1.17/0.52    inference(resolution,[],[f77,f52])).
% 1.17/0.52  fof(f52,plain,(
% 1.17/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f6])).
% 1.17/0.52  fof(f6,axiom,(
% 1.17/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.17/0.52  fof(f77,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 1.17/0.52    inference(resolution,[],[f63,f47])).
% 1.17/0.52  fof(f63,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f33])).
% 1.17/0.52  fof(f33,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(definition_folding,[],[f21,f32,f31])).
% 1.17/0.52  fof(f31,plain,(
% 1.17/0.52    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 1.17/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.17/0.52  fof(f21,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f20])).
% 1.17/0.52  fof(f20,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f12])).
% 1.17/0.52  fof(f12,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 1.17/0.52  fof(f58,plain,(
% 1.17/0.52    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | X0 = X3) )),
% 1.17/0.52    inference(cnf_transformation,[],[f42])).
% 1.17/0.52  fof(f42,plain,(
% 1.17/0.52    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.17/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.17/0.52  fof(f41,plain,(
% 1.17/0.52    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f40,plain,(
% 1.17/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.17/0.52    inference(rectify,[],[f39])).
% 1.17/0.52  fof(f39,plain,(
% 1.17/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.17/0.52    inference(flattening,[],[f38])).
% 1.17/0.52  fof(f38,plain,(
% 1.17/0.52    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.17/0.52    inference(nnf_transformation,[],[f31])).
% 1.17/0.52  fof(f122,plain,(
% 1.17/0.52    m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2))),
% 1.17/0.52    inference(subsumption_resolution,[],[f120,f67])).
% 1.17/0.52  fof(f120,plain,(
% 1.17/0.52    m1_subset_1(k1_tarski(sK5(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK5(u1_struct_0(sK2)),u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 1.17/0.52    inference(superposition,[],[f70,f114])).
% 1.17/0.52  fof(f70,plain,(
% 1.17/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f30])).
% 1.17/0.52  fof(f30,plain,(
% 1.17/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.17/0.52    inference(flattening,[],[f29])).
% 1.17/0.52  fof(f29,plain,(
% 1.17/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f10])).
% 1.17/0.52  fof(f10,axiom,(
% 1.17/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (24445)------------------------------
% 1.17/0.52  % (24445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (24445)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (24445)Memory used [KB]: 6268
% 1.17/0.52  % (24445)Time elapsed: 0.106 s
% 1.17/0.52  % (24445)------------------------------
% 1.17/0.52  % (24445)------------------------------
% 1.17/0.52  % (24441)Success in time 0.155 s
%------------------------------------------------------------------------------
