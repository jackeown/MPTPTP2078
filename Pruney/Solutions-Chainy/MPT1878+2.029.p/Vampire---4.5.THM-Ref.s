%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 (7602 expanded)
%              Number of leaves         :   14 (1573 expanded)
%              Depth                    :   22
%              Number of atoms          :  205 (31638 expanded)
%              Number of equality atoms :   19 ( 239 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(subsumption_resolution,[],[f157,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f157,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f71,f134])).

fof(f134,plain,(
    k1_xboole_0 = k1_tarski(sK4(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f122,f121])).

fof(f121,plain,(
    k1_xboole_0 = k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))) ),
    inference(unit_resulting_resolution,[],[f38,f63,f41,f102,f101,f42,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

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

fof(f101,plain,(
    m1_subset_1(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f99,f100])).

fof(f100,plain,(
    k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))) = k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))) ),
    inference(unit_resulting_resolution,[],[f78,f96,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f96,plain,(
    m1_subset_1(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f94,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
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

% (18890)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f94,plain,(
    m1_subset_1(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f92,f93])).

fof(f93,plain,(
    k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(sK3(sK0))))) = k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))) ),
    inference(unit_resulting_resolution,[],[f78,f89,f55])).

fof(f89,plain,(
    m1_subset_1(sK4(k1_tarski(sK4(sK3(sK0)))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f83,f57])).

fof(f83,plain,(
    m1_subset_1(k1_tarski(sK4(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f81,f82])).

fof(f82,plain,(
    k6_domain_1(u1_struct_0(sK0),sK4(sK3(sK0))) = k1_tarski(sK4(sK3(sK0))) ),
    inference(unit_resulting_resolution,[],[f78,f77,f55])).

fof(f77,plain,(
    m1_subset_1(sK4(sK3(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f76,f57])).

fof(f76,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f36,f38,f37,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    r2_hidden(sK4(sK3(sK0)),sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,(
    ~ v1_xboole_0(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f38,f37,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f78,f77,f56])).

fof(f56,plain,(
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

fof(f28,plain,(
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

fof(f92,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(sK3(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f78,f89,f56])).

fof(f65,plain,(
    ! [X0] : r2_hidden(sK4(k1_tarski(X0)),k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f53])).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f78,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f76,f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f99,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f78,f96,f56])).

fof(f102,plain,(
    v2_tex_2(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))),sK0) ),
    inference(forward_demodulation,[],[f98,f100])).

fof(f98,plain,(
    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f36,f96,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f63,plain,(
    v3_tex_2(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f35,f59])).

fof(f59,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f33,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f122,plain,(
    k1_xboole_0 = k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))) ),
    inference(unit_resulting_resolution,[],[f38,f63,f41,f110,f109,f42,f47])).

fof(f109,plain,(
    m1_subset_1(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f107,f108])).

fof(f108,plain,(
    k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))) = k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))) ),
    inference(unit_resulting_resolution,[],[f78,f104,f55])).

fof(f104,plain,(
    m1_subset_1(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f101,f57])).

fof(f107,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f78,f104,f56])).

fof(f110,plain,(
    v2_tex_2(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))),sK0) ),
    inference(forward_demodulation,[],[f106,f108])).

% (18890)Refutation not found, incomplete strategy% (18890)------------------------------
% (18890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18890)Termination reason: Refutation not found, incomplete strategy

% (18890)Memory used [KB]: 10618
% (18890)Time elapsed: 0.117 s
% (18890)------------------------------
% (18890)------------------------------
fof(f106,plain,(
    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f36,f104,f50])).

fof(f71,plain,(
    ! [X0] : ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f65,f39,f58])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (18895)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (18897)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (18889)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (18889)Refutation not found, incomplete strategy% (18889)------------------------------
% 0.21/0.50  % (18889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (18889)Memory used [KB]: 6140
% 0.21/0.50  % (18889)Time elapsed: 0.088 s
% 0.21/0.50  % (18889)------------------------------
% 0.21/0.50  % (18889)------------------------------
% 0.21/0.50  % (18905)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (18899)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (18897)Refutation not found, incomplete strategy% (18897)------------------------------
% 0.21/0.51  % (18897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18887)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (18897)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18897)Memory used [KB]: 6140
% 0.21/0.51  % (18897)Time elapsed: 0.104 s
% 0.21/0.51  % (18897)------------------------------
% 0.21/0.51  % (18897)------------------------------
% 0.21/0.51  % (18884)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (18909)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (18891)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (18901)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (18892)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (18907)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (18896)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (18893)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (18900)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (18885)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (18884)Refutation not found, incomplete strategy% (18884)------------------------------
% 0.21/0.52  % (18884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18884)Memory used [KB]: 10618
% 0.21/0.52  % (18884)Time elapsed: 0.106 s
% 0.21/0.52  % (18884)------------------------------
% 0.21/0.52  % (18884)------------------------------
% 0.21/0.53  % (18903)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (18898)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (18891)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.53    inference(superposition,[],[f71,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    k1_xboole_0 = k1_tarski(sK4(k1_xboole_0))),
% 0.21/0.53    inference(backward_demodulation,[],[f122,f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    k1_xboole_0 = k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f38,f63,f41,f102,f101,f42,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(forward_demodulation,[],[f99,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))) = k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f96,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    m1_subset_1(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))),u1_struct_0(sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f65,f94,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  % (18890)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(forward_demodulation,[],[f92,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(sK3(sK0))))) = k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f89,f55])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    m1_subset_1(sK4(k1_tarski(sK4(sK3(sK0)))),u1_struct_0(sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f65,f83,f57])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK4(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(forward_demodulation,[],[f81,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4(sK3(sK0))) = k1_tarski(sK4(sK3(sK0)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f77,f55])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    m1_subset_1(sK4(sK3(sK0)),u1_struct_0(sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f69,f76,f57])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f36,f38,f37,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    r2_hidden(sK4(sK3(sK0)),sK3(sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f68,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ~v1_xboole_0(sK3(sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f36,f38,f37,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f77,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(sK3(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f89,f56])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK4(k1_tarski(X0)),k1_tarski(X0))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f40,f53])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f69,f76,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f96,f56])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    v2_tex_2(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))),sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f98,f100])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))),sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f37,f38,f36,f96,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    v3_tex_2(k1_xboole_0,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f35,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f33,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v1_xboole_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v3_tex_2(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    k1_xboole_0 = k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))))))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f38,f63,f41,f110,f109,f42,f47])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(forward_demodulation,[],[f107,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))) = k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))))))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f104,f55])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    m1_subset_1(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0)))))))),u1_struct_0(sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f65,f101,f57])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f104,f56])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    v2_tex_2(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))),sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f106,f108])).
% 0.21/0.53  % (18890)Refutation not found, incomplete strategy% (18890)------------------------------
% 0.21/0.53  % (18890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18890)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18890)Memory used [KB]: 10618
% 0.21/0.53  % (18890)Time elapsed: 0.117 s
% 0.21/0.53  % (18890)------------------------------
% 0.21/0.53  % (18890)------------------------------
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(k1_tarski(sK4(k1_tarski(sK4(k1_tarski(sK4(sK3(sK0))))))))),sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f37,f38,f36,f104,f50])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f65,f39,f58])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (18891)------------------------------
% 0.21/0.53  % (18891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18891)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (18891)Memory used [KB]: 1791
% 0.21/0.53  % (18891)Time elapsed: 0.085 s
% 0.21/0.53  % (18891)------------------------------
% 0.21/0.53  % (18891)------------------------------
% 0.21/0.53  % (18883)Success in time 0.167 s
%------------------------------------------------------------------------------
