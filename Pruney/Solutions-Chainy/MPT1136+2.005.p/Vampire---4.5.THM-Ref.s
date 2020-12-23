%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 101 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 ( 331 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f87])).

fof(f87,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f85,f25])).

fof(f25,plain,(
    ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_orders_2(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(f85,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f84,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f83,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f33,f79])).

fof(f79,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f64,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f62,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f62,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f61,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f30,f28])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f75,f58])).

fof(f58,plain,(
    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f57,f28])).

fof(f57,plain,
    ( r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f32,f27])).

fof(f27,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v3_orders_2(X0)
      | r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r1_relat_2(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK1,sK1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f56,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f53,f42])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f29,f28])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f53,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f51,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f43,f49,f45])).

fof(f43,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:41:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (30670)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.46  % (30670)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f52,f56,f87])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    $false | ~spl3_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f85,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ~r1_orders_2(sK0,sK1,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r1_orders_2(X0,X1,X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r1_orders_2(X0,X1,X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    r1_orders_2(sK0,sK1,sK1) | ~spl3_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f84,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    l1_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ~l1_orders_2(sK0) | r1_orders_2(sK0,sK1,sK1) | ~spl3_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f83,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK1,sK1) | ~spl3_1),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK1,sK1) | ~spl3_1),
% 0.21/0.46    inference(resolution,[],[f33,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) | ~spl3_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f78,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    v1_relat_1(u1_orders_2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f62,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) | v1_relat_1(u1_orders_2(sK0))),
% 0.21/0.46    inference(resolution,[],[f61,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.46    inference(resolution,[],[f30,f28])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) | ~v1_relat_1(u1_orders_2(sK0)) | ~spl3_1),
% 0.21/0.46    inference(resolution,[],[f75,f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f57,f28])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.46    inference(resolution,[],[f32,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    v3_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0] : (~v3_orders_2(X0) | r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : ((v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) => (v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_relat_2(X0,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK1),X0) | ~v1_relat_1(X0)) ) | ~spl3_1),
% 0.21/0.46    inference(resolution,[],[f36,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl3_1 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X2,X2),X0) | ~r1_relat_2(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ~spl3_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    $false | ~spl3_2),
% 0.21/0.46    inference(subsumption_resolution,[],[f54,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    v2_struct_0(sK0) | ~spl3_2),
% 0.21/0.46    inference(subsumption_resolution,[],[f53,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    l1_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f29,f28])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_2),
% 0.21/0.46    inference(resolution,[],[f51,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl3_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl3_1 | spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f43,f49,f45])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(resolution,[],[f41,f24])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (30670)------------------------------
% 0.21/0.46  % (30670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (30670)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (30670)Memory used [KB]: 5373
% 0.21/0.46  % (30670)Time elapsed: 0.045 s
% 0.21/0.46  % (30670)------------------------------
% 0.21/0.46  % (30670)------------------------------
% 0.21/0.47  % (30663)Success in time 0.101 s
%------------------------------------------------------------------------------
