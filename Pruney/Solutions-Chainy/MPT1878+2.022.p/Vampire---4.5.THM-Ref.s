%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 344 expanded)
%              Number of leaves         :   15 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 (1175 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f39,f65,f70,f40,f124,f123,f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f123,plain,(
    m1_subset_1(k1_tarski(sK4(sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f121,f122])).

fof(f122,plain,(
    k6_domain_1(u1_struct_0(sK0),sK4(sK2(u1_struct_0(sK0)))) = k1_tarski(sK4(sK2(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f82,f118,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f118,plain,(
    m1_subset_1(sK4(sK2(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f83,f87,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f87,plain,(
    r2_hidden(sK4(sK2(u1_struct_0(sK0))),sK2(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f85,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f85,plain,(
    ~ v1_xboole_0(sK2(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f82,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

fof(f83,plain,(
    m1_subset_1(sK2(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f82,f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f61,f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f121,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f82,f118,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f124,plain,(
    v2_tex_2(k1_tarski(sK4(sK2(u1_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f120,f122])).

fof(f120,plain,(
    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(sK2(u1_struct_0(sK0)))),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f118,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f57,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f65,plain,(
    v3_tex_2(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f36,f62])).

fof(f62,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f34,f52])).

fof(f52,plain,(
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

fof(f34,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (16929)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.46  % (16937)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.46  % (16929)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f162,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f39,f65,f70,f40,f124,f123,f41,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    m1_subset_1(k1_tarski(sK4(sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f121,f122])).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    k6_domain_1(u1_struct_0(sK0),sK4(sK2(u1_struct_0(sK0)))) = k1_tarski(sK4(sK2(u1_struct_0(sK0))))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f82,f118,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK2(u1_struct_0(sK0))),u1_struct_0(sK0))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f83,f87,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    r2_hidden(sK4(sK2(u1_struct_0(sK0))),sK2(u1_struct_0(sK0)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f85,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ~v1_xboole_0(sK2(u1_struct_0(sK0)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f82,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(sK2(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(X0) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    m1_subset_1(sK2(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f82,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f37,f61,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    l1_struct_0(sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f39,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~v2_struct_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.46    inference(negated_conjecture,[],[f15])).
% 0.20/0.46  fof(f15,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4(sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f82,f118,f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    v2_tex_2(k1_tarski(sK4(sK2(u1_struct_0(sK0)))),sK0)),
% 0.20/0.48    inference(forward_demodulation,[],[f120,f122])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(sK2(u1_struct_0(sK0)))),sK0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f37,f38,f39,f118,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.20/0.48    inference(superposition,[],[f57,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    v3_tex_2(k1_xboole_0,sK0)),
% 0.20/0.48    inference(backward_demodulation,[],[f36,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    k1_xboole_0 = sK1),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f34,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    v1_xboole_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (16929)------------------------------
% 0.20/0.48  % (16929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (16929)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (16929)Memory used [KB]: 1791
% 0.20/0.48  % (16929)Time elapsed: 0.074 s
% 0.20/0.48  % (16929)------------------------------
% 0.20/0.48  % (16929)------------------------------
% 0.20/0.48  % (16921)Success in time 0.126 s
%------------------------------------------------------------------------------
