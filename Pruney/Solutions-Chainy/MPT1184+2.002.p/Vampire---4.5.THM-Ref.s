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
% DateTime   : Thu Dec  3 13:10:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 136 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 ( 850 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f57])).

fof(f57,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f56,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f56,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f51,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(sK1,sK0) )
    & r3_orders_1(u1_orders_2(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X1,X0) )
            & r3_orders_1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X1,sK0) )
          & r3_orders_1(u1_orders_2(sK0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v6_orders_2(X1,sK0) )
        & r3_orders_1(u1_orders_2(sK0),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(sK1,sK0) )
      & r3_orders_1(u1_orders_2(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r3_orders_1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r3_orders_1(u1_orders_2(X0),X1)
           => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_orders_2)).

fof(f32,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f65,plain,(
    ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f64,f61])).

fof(f61,plain,(
    r1_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f47,f57])).

fof(f47,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | r1_relat_2(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_1(X0,X1)
      | r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).

fof(f64,plain,
    ( ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f63,f55])).

fof(f55,plain,(
    ~ r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f54,f28])).

fof(f54,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f53,f45])).

fof(f45,plain,(
    ~ v6_orders_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f31,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | v6_orders_2(sK1,sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f34,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f63,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X1,X0)
      | r7_relat_2(X1,X0)
      | ~ r1_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

fof(f58,plain,(
    r6_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f50,f57])).

fof(f50,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | r6_relat_2(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f39,f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_1(X0,X1)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (3608)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % (3606)WARNING: option uwaf not known.
% 0.20/0.46  % (3614)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (3606)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.47  % (3606)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f65,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f56,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    v1_relat_1(u1_orders_2(sK0)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.20/0.47    inference(resolution,[],[f51,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.20/0.47    inference(resolution,[],[f32,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    l1_orders_2(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(sK1,sK0)) & r3_orders_1(u1_orders_2(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r3_orders_1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X1,sK0)) & r3_orders_1(u1_orders_2(sK0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X1,sK0)) & r3_orders_1(u1_orders_2(sK0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(sK1,sK0)) & r3_orders_1(u1_orders_2(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r3_orders_1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r3_orders_1(u1_orders_2(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r3_orders_1(u1_orders_2(X0),X1) => (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r3_orders_1(u1_orders_2(X0),X1) => (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_orders_2)).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ~v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f64,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    r1_relat_2(u1_orders_2(sK0),sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f47,f57])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ~v1_relat_1(u1_orders_2(sK0)) | r1_relat_2(u1_orders_2(sK0),sK1)),
% 0.20/0.47    inference(resolution,[],[f36,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r3_orders_1(X0,X1) | r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r3_orders_1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1)) & ((r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r3_orders_1(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r3_orders_1(X0,X1) | (~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1))) & ((r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r3_orders_1(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r3_orders_1(X0,X1) <=> (r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r3_orders_1(X0,X1) <=> (r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ~r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f63,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ~r7_relat_2(u1_orders_2(sK0),sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f54,f28])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ~r7_relat_2(u1_orders_2(sK0),sK1) | ~l1_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f53,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ~v6_orders_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f31,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ~r7_relat_2(u1_orders_2(sK0),sK1) | v6_orders_2(sK1,sK0) | ~l1_orders_2(sK0)),
% 0.20/0.47    inference(resolution,[],[f34,f29])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r7_relat_2(u1_orders_2(X0),X1) | v6_orders_2(X1,X0) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1)) & (r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    r7_relat_2(u1_orders_2(sK0),sK1) | ~r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.47    inference(resolution,[],[f58,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r6_relat_2(X1,X0) | r7_relat_2(X1,X0) | ~r1_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (((r7_relat_2(X1,X0) | ~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0)) & ((r6_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~r7_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (((r7_relat_2(X1,X0) | (~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0))) & ((r6_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~r7_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    r6_relat_2(u1_orders_2(sK0),sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f50,f57])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ~v1_relat_1(u1_orders_2(sK0)) | r6_relat_2(u1_orders_2(sK0),sK1)),
% 0.20/0.47    inference(resolution,[],[f39,f30])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r3_orders_1(X0,X1) | r6_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (3606)------------------------------
% 0.20/0.47  % (3606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3606)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (3606)Memory used [KB]: 895
% 0.20/0.47  % (3606)Time elapsed: 0.067 s
% 0.20/0.47  % (3606)------------------------------
% 0.20/0.47  % (3606)------------------------------
% 0.20/0.47  % (3600)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.47  % (3595)Success in time 0.12 s
%------------------------------------------------------------------------------
