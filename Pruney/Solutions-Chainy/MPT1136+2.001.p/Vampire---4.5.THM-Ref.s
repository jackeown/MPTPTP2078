%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  95 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   16
%              Number of atoms          :  157 ( 323 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f125])).

fof(f125,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f123,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_orders_2(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f123,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f120,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f46,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f46,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f114,f23])).

fof(f23,plain,(
    ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f114,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f113,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f112,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | spl3_1 ),
    inference(resolution,[],[f34,f84])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f83,f60])).

fof(f60,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f59,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f59,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f31,f26])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f83,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | spl3_1 ),
    inference(resolution,[],[f79,f57])).

fof(f57,plain,(
    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f56,f26])).

fof(f56,plain,
    ( r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r1_relat_2(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK1,sK1),X0)
        | ~ v1_relat_1(X0) )
    | spl3_1 ),
    inference(resolution,[],[f27,f54])).

fof(f54,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f53,f47])).

fof(f47,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f53,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8486)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.47  % (8483)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.47  % (8486)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f116,f125])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f124])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    $false | ~spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f123,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ~v2_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (~r1_orders_2(X0,X1,X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (~r1_orders_2(X0,X1,X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f9])).
% 0.22/0.47  fof(f9,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    v2_struct_0(sK0) | ~spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f120,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    l1_struct_0(sK0)),
% 0.22/0.47    inference(resolution,[],[f30,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    l1_orders_2(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_1),
% 0.22/0.47    inference(resolution,[],[f46,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl3_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    $false | spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f114,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ~r1_orders_2(sK0,sK1,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    r1_orders_2(sK0,sK1,sK1) | spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f113,f26])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~l1_orders_2(sK0) | r1_orders_2(sK0,sK1,sK1) | spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f112,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK1,sK1) | spl3_1),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK1,sK1) | spl3_1),
% 0.22/0.47    inference(resolution,[],[f34,f84])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) | spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f83,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    v1_relat_1(u1_orders_2(sK0))),
% 0.22/0.47    inference(resolution,[],[f59,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.47    inference(resolution,[],[f31,f26])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) | ~v1_relat_1(u1_orders_2(sK0)) | spl3_1),
% 0.22/0.47    inference(resolution,[],[f79,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f56,f26])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.22/0.47    inference(resolution,[],[f33,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    v3_orders_2(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0] : (~v3_orders_2(X0) | r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : ((v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => (v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_relat_2(X0,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK1),X0) | ~v1_relat_1(X0)) ) | spl3_1),
% 0.22/0.47    inference(resolution,[],[f27,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    r2_hidden(sK1,u1_struct_0(sK0)) | spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f53,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f45])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    r2_hidden(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f40,f22])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X2,X2),X0) | ~r1_relat_2(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (8486)------------------------------
% 0.22/0.47  % (8486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (8486)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (8486)Memory used [KB]: 5373
% 0.22/0.47  % (8486)Time elapsed: 0.058 s
% 0.22/0.47  % (8486)------------------------------
% 0.22/0.47  % (8486)------------------------------
% 0.22/0.47  % (8479)Success in time 0.109 s
%------------------------------------------------------------------------------
