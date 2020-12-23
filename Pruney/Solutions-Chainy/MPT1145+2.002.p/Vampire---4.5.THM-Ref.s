%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  77 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 343 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52,f45])).

fof(f45,plain,(
    ~ r7_relat_2(u1_orders_2(sK0),sK2) ),
    inference(subsumption_resolution,[],[f44,f27])).

fof(f27,plain,(
    ~ v6_orders_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f15,f16])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X2,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,X1)
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_orders_2)).

fof(f15,plain,
    ( ~ v6_orders_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK2)
    | v6_orders_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f42,f20])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r7_relat_2(u1_orders_2(sK0),sK2)
    | v6_orders_2(sK2,sK0) ),
    inference(resolution,[],[f22,f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(f52,plain,(
    r7_relat_2(u1_orders_2(sK0),sK2) ),
    inference(resolution,[],[f51,f17])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r7_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f50,f41])).

fof(f41,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f40,f25])).

fof(f25,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f40,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f39,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f21,f20])).

fof(f21,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(u1_orders_2(sK0))
      | ~ r1_tarski(X0,sK1)
      | r7_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | r7_relat_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r7_relat_2(X2,X0) )
       => r7_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_orders_1)).

fof(f49,plain,(
    r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f48,f18])).

fof(f18,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v6_orders_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f47,f20])).

fof(f47,plain,
    ( ~ l1_orders_2(sK0)
    | r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v6_orders_2(sK1,sK0) ),
    inference(resolution,[],[f23,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:52:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (11225)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.47  % (11225)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f52,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~r7_relat_2(u1_orders_2(sK0),sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f44,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ~v6_orders_2(sK2,sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f15,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) & l1_orders_2(X0))),
% 0.22/0.47    inference(flattening,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) & r1_tarski(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0))) & l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_orders_2(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_orders_2)).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ~v6_orders_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ~r7_relat_2(u1_orders_2(sK0),sK2) | v6_orders_2(sK2,sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f42,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    l1_orders_2(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ~l1_orders_2(sK0) | ~r7_relat_2(u1_orders_2(sK0),sK2) | v6_orders_2(sK2,sK0)),
% 0.22/0.47    inference(resolution,[],[f22,f16])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~r7_relat_2(u1_orders_2(X0),X1) | v6_orders_2(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    r7_relat_2(u1_orders_2(sK0),sK2)),
% 0.22/0.47    inference(resolution,[],[f51,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    r1_tarski(sK2,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(X0,sK1) | r7_relat_2(u1_orders_2(sK0),X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f50,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    v1_relat_1(u1_orders_2(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f40,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) | v1_relat_1(u1_orders_2(sK0))),
% 0.22/0.47    inference(resolution,[],[f39,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.47    inference(resolution,[],[f21,f20])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_relat_1(u1_orders_2(sK0)) | ~r1_tarski(X0,sK1) | r7_relat_2(u1_orders_2(sK0),X0)) )),
% 0.22/0.47    inference(resolution,[],[f49,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r7_relat_2(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X1,X0) | r7_relat_2(X2,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r7_relat_2(X2,X1) | ~r1_tarski(X1,X0) | ~r7_relat_2(X2,X0) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r7_relat_2(X2,X1) | (~r1_tarski(X1,X0) | ~r7_relat_2(X2,X0))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(X1,X0) & r7_relat_2(X2,X0)) => r7_relat_2(X2,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_orders_1)).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    r7_relat_2(u1_orders_2(sK0),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f48,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    v6_orders_2(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    r7_relat_2(u1_orders_2(sK0),sK1) | ~v6_orders_2(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f47,f20])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ~l1_orders_2(sK0) | r7_relat_2(u1_orders_2(sK0),sK1) | ~v6_orders_2(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f23,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (11225)------------------------------
% 0.22/0.48  % (11225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (11225)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (11225)Memory used [KB]: 5373
% 0.22/0.48  % (11225)Time elapsed: 0.053 s
% 0.22/0.48  % (11225)------------------------------
% 0.22/0.48  % (11225)------------------------------
% 0.22/0.48  % (11218)Success in time 0.109 s
%------------------------------------------------------------------------------
