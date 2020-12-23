%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 (3531 expanded)
%              Number of leaves         :   17 ( 668 expanded)
%              Depth                    :   58
%              Number of atoms          :  518 (12747 expanded)
%              Number of equality atoms :   77 ( 920 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(subsumption_resolution,[],[f334,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f334,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f332,f58])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f332,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f331,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f331,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f330,f65])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f330,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f329,f51])).

fof(f329,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f328,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f328,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f327,f52])).

fof(f327,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f322,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f322,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f320,f299])).

fof(f299,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f247,f288])).

fof(f288,plain,
    ( ~ v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f242,f80])).

fof(f80,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f242,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f82,f241])).

fof(f241,plain,(
    u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(global_subsumption,[],[f84,f175,f240])).

fof(f240,plain,
    ( ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f237,f50])).

fof(f237,plain,
    ( ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f207,f92])).

fof(f92,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f91,f52])).

fof(f91,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f90,f58])).

fof(f90,plain,
    ( ~ l1_struct_0(sK0)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f89,f51])).

fof(f89,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f87,f65])).

fof(f87,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f78,f50])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f72,f53])).

% (21508)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f207,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f203,f175])).

fof(f203,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = k2_tarski(sK1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f195,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f195,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f190,f154])).

fof(f154,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f146,f124])).

fof(f124,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f123,f52])).

fof(f123,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f122,f58])).

fof(f122,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f121,f51])).

fof(f121,plain,
    ( u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f119,f65])).

fof(f119,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f117,f84])).

fof(f117,plain,
    ( ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f116,f50])).

fof(f116,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f103,f98])).

fof(f98,plain,(
    ! [X0] :
      ( m1_pre_topc(k1_tex_2(sK0,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f97,f51])).

fof(f97,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_pre_topc(k1_tex_2(sK0,X0),sK0) ) ),
    inference(resolution,[],[f74,f52])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f102,f52])).

fof(f102,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f62,f94])).

fof(f94,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f49,f92])).

fof(f49,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f146,plain,
    ( u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f145,f52])).

fof(f145,plain,
    ( u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f144,f58])).

fof(f144,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f143,f51])).

fof(f143,plain,
    ( u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f141,f65])).

fof(f141,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f138,f84])).

fof(f138,plain,
    ( ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f137,f50])).

fof(f137,plain,
    ( u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f136,f98])).

fof(f136,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f135,f94])).

fof(f135,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f134,f52])).

fof(f134,plain,
    ( u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f112,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f112,plain,
    ( v1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f111,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,
    ( m1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f110,f50])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,X0),sK0)
      | m1_subset_1(sK3(sK0,k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f109,f52])).

fof(f109,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | m1_subset_1(sK3(sK0,k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tex_2(k1_tex_2(sK0,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f61,f98])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f190,plain,(
    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(resolution,[],[f189,f50])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f188,f52])).

fof(f188,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f187,f51])).

fof(f187,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f185,f100])).

fof(f100,plain,(
    ! [X0] :
      ( l1_pre_topc(k1_tex_2(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f99,f52])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | l1_pre_topc(k1_tex_2(sK0,X0)) ) ),
    inference(resolution,[],[f98,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(k1_tex_2(X1,X0))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f86,f58])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0,X1))) ) ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f175,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f174,f50])).

fof(f174,plain,
    ( u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f173,f100])).

fof(f173,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f172,f58])).

fof(f172,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f171,f51])).

fof(f171,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f170,f50])).

fof(f170,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f52])).

fof(f169,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f160,f73])).

fof(f160,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f65,f154])).

fof(f84,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f70,f82])).

fof(f82,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f77,f81])).

fof(f81,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f69,f50])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ) ),
    inference(definition_unfolding,[],[f68,f53])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f247,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f93,f241])).

fof(f93,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f48,f92])).

fof(f48,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f320,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f286,f50])).

fof(f286,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,X0),sK0)
      | v2_struct_0(k1_tex_2(sK0,X0)) ) ),
    inference(resolution,[],[f279,f98])).

fof(f279,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ v1_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f278,f52])).

fof(f278,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ v1_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f276,f51])).

fof(f276,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ v1_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f275,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f275,plain,(
    v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f274,f52])).

fof(f274,plain,
    ( v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f273,f58])).

fof(f273,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f272,f51])).

fof(f272,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f271,f65])).

fof(f271,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f270,f52])).

fof(f270,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f261,f58])).

fof(f261,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v7_struct_0(sK0) ),
    inference(resolution,[],[f257,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f257,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f96,f241])).

fof(f96,plain,
    ( u1_struct_0(sK0) != k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f95,f50])).

fof(f95,plain,
    ( u1_struct_0(sK0) != k2_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(superposition,[],[f56,f92])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (21500)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.47  % (21516)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.47  % (21500)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f335,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f334,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f17])).
% 0.20/0.47  fof(f17,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.20/0.47  fof(f334,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0)),
% 0.20/0.47    inference(resolution,[],[f332,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.47  fof(f332,plain,(
% 0.20/0.47    ~l1_struct_0(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f331,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f331,plain,(
% 0.20/0.47    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f330,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.47  fof(f330,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f329,f51])).
% 0.20/0.47  fof(f329,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f328,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f328,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f327,f52])).
% 0.20/0.47  fof(f327,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f322,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.20/0.47  fof(f322,plain,(
% 0.20/0.47    v2_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f320,f299])).
% 0.20/0.47  fof(f299,plain,(
% 0.20/0.47    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f247,f288])).
% 0.20/0.47  fof(f288,plain,(
% 0.20/0.47    ~v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f242,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    inference(backward_demodulation,[],[f82,f241])).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(global_subsumption,[],[f84,f175,f240])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f237,f50])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(superposition,[],[f207,f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f91,f52])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.47    inference(resolution,[],[f90,f58])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ~l1_struct_0(sK0) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f89,f51])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f87,f65])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(resolution,[],[f78,f50])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f72,f53])).
% 0.20/0.47  % (21508)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f203,f175])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    ( ! [X0] : (u1_struct_0(sK0) = k2_tarski(sK1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.20/0.47    inference(resolution,[],[f195,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,axiom,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(superposition,[],[f190,f154])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f147])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(superposition,[],[f146,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f123,f52])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.47    inference(resolution,[],[f122,f58])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ~l1_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f121,f51])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    u1_struct_0(sK0) = k2_tarski(sK1,sK1) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f119,f65])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.20/0.47    inference(resolution,[],[f117,f84])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.20/0.47    inference(subsumption_resolution,[],[f116,f50])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f103,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0] : (m1_pre_topc(k1_tex_2(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f97,f51])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_pre_topc(k1_tex_2(sK0,X0),sK0)) )),
% 0.20/0.47    inference(resolution,[],[f74,f52])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f45])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f102,f52])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f62,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))),
% 0.20/0.47    inference(backward_demodulation,[],[f49,f92])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f145,f52])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.47    inference(resolution,[],[f144,f58])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ~l1_struct_0(sK0) | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f143,f51])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    u1_struct_0(sK0) = k2_tarski(sK1,sK1) | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f141,f65])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.20/0.47    inference(resolution,[],[f138,f84])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.20/0.47    inference(subsumption_resolution,[],[f137,f50])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f136,f98])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f135,f94])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f134,f52])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.47    inference(resolution,[],[f112,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    v1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.47    inference(resolution,[],[f111,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f41])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    m1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.47    inference(resolution,[],[f110,f50])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X0),sK0) | m1_subset_1(sK3(sK0,k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f109,f52])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | m1_subset_1(sK3(sK0,k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(resolution,[],[f61,f98])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.47    inference(resolution,[],[f189,f50])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,X0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f188,f52])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,X0))) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f187,f51])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,X0))) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f186])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,X0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(resolution,[],[f185,f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0] : (l1_pre_topc(k1_tex_2(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f99,f52])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | l1_pre_topc(k1_tex_2(sK0,X0))) )),
% 0.20/0.47    inference(resolution,[],[f98,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(k1_tex_2(X1,X0)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.47    inference(resolution,[],[f86,f58])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0,X1)))) )),
% 0.20/0.47    inference(resolution,[],[f76,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    ~v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f174,f50])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    u1_struct_0(sK0) = k2_tarski(sK1,sK1) | ~v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f173,f100])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f172,f58])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f171,f51])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f170,f50])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f169,f52])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f160,f73])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.48    inference(superposition,[],[f65,f154])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f70,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f77,f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    r2_hidden(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f69,f50])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f68,f53])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f93,f241])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f48,f92])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.49    inference(resolution,[],[f286,f50])).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X0),sK0) | v2_struct_0(k1_tex_2(sK0,X0))) )),
% 0.20/0.49    inference(resolution,[],[f279,f98])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v1_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f278,f52])).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v1_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f276,f51])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v1_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f275,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v1_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    v7_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f274,f52])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    v7_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(resolution,[],[f273,f58])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | v7_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f272,f51])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    v7_struct_0(sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f271,f65])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK0)) | v7_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f270,f52])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK0)) | v7_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(resolution,[],[f261,f58])).
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | v7_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f257,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f249])).
% 0.20/0.49  fof(f249,plain,(
% 0.20/0.49    u1_struct_0(sK0) != u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.49    inference(backward_demodulation,[],[f96,f241])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    u1_struct_0(sK0) != k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f95,f50])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    u1_struct_0(sK0) != k2_tarski(sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.49    inference(superposition,[],[f56,f92])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (21500)------------------------------
% 0.20/0.49  % (21500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21500)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (21500)Memory used [KB]: 6524
% 0.20/0.49  % (21500)Time elapsed: 0.091 s
% 0.20/0.49  % (21500)------------------------------
% 0.20/0.49  % (21500)------------------------------
% 0.20/0.49  % (21493)Success in time 0.136 s
%------------------------------------------------------------------------------
