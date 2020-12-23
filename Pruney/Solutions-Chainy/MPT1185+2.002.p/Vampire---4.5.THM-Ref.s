%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 266 expanded)
%              Number of leaves         :   19 (  78 expanded)
%              Depth                    :   20
%              Number of atoms          :  384 (1402 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f128,f131,f162])).

fof(f162,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f160,f48])).

fof(f48,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r3_orders_1(u1_orders_2(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v6_orders_2(sK1,sK0)
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_orders_1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(sK0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v6_orders_2(X1,sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ r3_orders_1(u1_orders_2(sK0),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(X1,sK0) )
   => ( ~ r3_orders_1(u1_orders_2(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v6_orders_2(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_orders_2)).

fof(f160,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f159,f46])).

fof(f46,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f159,plain,
    ( ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f156,f147])).

fof(f147,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f146,f117])).

fof(f117,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_3
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f146,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f145,f127])).

fof(f127,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_5
  <=> r1_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f145,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f144,f141])).

fof(f141,plain,(
    r4_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f140,f48])).

% (4675)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
fof(f140,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f137,f47])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f137,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f102,f99])).

fof(f99,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f96,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0,u1_struct_0(sK0)),sK1)
      | r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f92,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f69,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | r4_relat_2(u1_orders_2(X1),X0)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f101,f95])).

fof(f95,plain,(
    ! [X2] :
      ( v1_relat_1(u1_orders_2(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f94,plain,(
    ! [X2] :
      ( ~ l1_orders_2(X2)
      | v1_relat_1(u1_orders_2(X2))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))) ) ),
    inference(resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | r4_relat_2(u1_orders_2(X1),X0)
      | ~ v1_relat_1(u1_orders_2(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f73,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_relat_2(X2,X0)
      | ~ r1_tarski(X1,X0)
      | r4_relat_2(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r4_relat_2(X2,X0) )
       => r4_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_orders_1)).

fof(f144,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f143,f51])).

fof(f51,plain,(
    ~ r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f143,plain,
    ( r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f64,f122])).

fof(f122,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_4
  <=> r6_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X0,X1)
      | r3_orders_1(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).

fof(f156,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f104,f99])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | r8_relat_2(u1_orders_2(X1),X0)
      | ~ v4_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f103,f95])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | r8_relat_2(u1_orders_2(X1),X0)
      | ~ v1_relat_1(u1_orders_2(X1))
      | ~ v4_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f74,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r8_relat_2(X2,X0)
      | ~ r1_tarski(X1,X0)
      | r8_relat_2(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r8_relat_2(X2,X0) )
       => r8_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_orders_1)).

fof(f131,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f129,f48])).

fof(f129,plain,
    ( ~ l1_orders_2(sK0)
    | spl3_3 ),
    inference(resolution,[],[f118,f95])).

fof(f118,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f128,plain,
    ( ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f114,f125,f116])).

fof(f114,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f112,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X1,X0)
      | r1_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

fof(f112,plain,(
    r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f49,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f110,plain,
    ( ~ v6_orders_2(sK1,sK0)
    | r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f57,f50])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X1,X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f123,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f113,f120,f116])).

fof(f113,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f112,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X1,X0)
      | r6_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (4685)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (4689)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.48  % (4680)WARNING: option uwaf not known.
% 0.21/0.48  % (4685)Refutation not found, incomplete strategy% (4685)------------------------------
% 0.21/0.48  % (4685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4685)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4685)Memory used [KB]: 895
% 0.21/0.48  % (4685)Time elapsed: 0.006 s
% 0.21/0.48  % (4685)------------------------------
% 0.21/0.48  % (4685)------------------------------
% 0.21/0.48  % (4672)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.48  % (4677)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % (4689)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (4680)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f123,f128,f131,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    $false | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f160,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    l1_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    (~r3_orders_1(u1_orders_2(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(sK1,sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f31,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r3_orders_1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r3_orders_1(u1_orders_2(sK0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(X1,sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X1] : (~r3_orders_1(u1_orders_2(sK0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(X1,sK0)) => (~r3_orders_1(u1_orders_2(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(sK1,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r3_orders_1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r3_orders_1(u1_orders_2(X0),X1) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) => r3_orders_1(u1_orders_2(X0),X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) => r3_orders_1(u1_orders_2(X0),X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_orders_2)).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f159,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    v4_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~v4_orders_2(sK0) | ~l1_orders_2(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f156,f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~r8_relat_2(u1_orders_2(sK0),sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f146,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    v1_relat_1(u1_orders_2(sK0)) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl3_3 <=> v1_relat_1(u1_orders_2(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ~r8_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | (~spl3_4 | ~spl3_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f145,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    r1_relat_2(u1_orders_2(sK0),sK1) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl3_5 <=> r1_relat_2(u1_orders_2(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | ~spl3_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f144,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    r4_relat_2(u1_orders_2(sK0),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f140,f48])).
% 0.21/0.49  % (4675)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    r4_relat_2(u1_orders_2(sK0),sK1) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f137,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v5_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    r4_relat_2(u1_orders_2(sK0),sK1) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(resolution,[],[f102,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f96,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK2(X0,u1_struct_0(sK0)),sK1) | r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.21/0.49    inference(resolution,[],[f92,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f69,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | r4_relat_2(u1_orders_2(X1),X0) | ~v5_orders_2(X1) | ~l1_orders_2(X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f101,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2] : (v1_relat_1(u1_orders_2(X2)) | ~l1_orders_2(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X2] : (~l1_orders_2(X2) | v1_relat_1(u1_orders_2(X2)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))) )),
% 0.21/0.49    inference(resolution,[],[f52,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | r4_relat_2(u1_orders_2(X1),X0) | ~v1_relat_1(u1_orders_2(X1)) | ~v5_orders_2(X1) | ~l1_orders_2(X1)) )),
% 0.21/0.49    inference(resolution,[],[f73,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (((v5_orders_2(X0) | ~r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r4_relat_2(X2,X0) | ~r1_tarski(X1,X0) | r4_relat_2(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r4_relat_2(X2,X1) | ~r1_tarski(X1,X0) | ~r4_relat_2(X2,X0) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r4_relat_2(X2,X1) | (~r1_tarski(X1,X0) | ~r4_relat_2(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(X1,X0) & r4_relat_2(X2,X0)) => r4_relat_2(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_orders_1)).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~r4_relat_2(u1_orders_2(sK0),sK1) | ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | ~spl3_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f143,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    r3_orders_1(u1_orders_2(sK0),sK1) | ~r4_relat_2(u1_orders_2(sK0),sK1) | ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f64,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    r6_relat_2(u1_orders_2(sK0),sK1) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl3_4 <=> r6_relat_2(u1_orders_2(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r6_relat_2(X0,X1) | r3_orders_1(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r3_orders_1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1)) & ((r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r3_orders_1(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r3_orders_1(X0,X1) | (~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1))) & ((r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r3_orders_1(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r3_orders_1(X0,X1) <=> (r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r3_orders_1(X0,X1) <=> (r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    r8_relat_2(u1_orders_2(sK0),sK1) | ~v4_orders_2(sK0) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(resolution,[],[f104,f99])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | r8_relat_2(u1_orders_2(X1),X0) | ~v4_orders_2(X1) | ~l1_orders_2(X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f103,f95])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | r8_relat_2(u1_orders_2(X1),X0) | ~v1_relat_1(u1_orders_2(X1)) | ~v4_orders_2(X1) | ~l1_orders_2(X1)) )),
% 0.21/0.49    inference(resolution,[],[f74,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v4_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (((v4_orders_2(X0) | ~r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v4_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : ((v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => (v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r8_relat_2(X2,X0) | ~r1_tarski(X1,X0) | r8_relat_2(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r8_relat_2(X2,X1) | ~r1_tarski(X1,X0) | ~r8_relat_2(X2,X0) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r8_relat_2(X2,X1) | (~r1_tarski(X1,X0) | ~r8_relat_2(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(X1,X0) & r8_relat_2(X2,X0)) => r8_relat_2(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_orders_1)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    $false | spl3_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f48])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | spl3_3),
% 0.21/0.49    inference(resolution,[],[f118,f95])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~v1_relat_1(u1_orders_2(sK0)) | spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~spl3_3 | spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f114,f125,f116])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.21/0.49    inference(resolution,[],[f112,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r7_relat_2(X1,X0) | r1_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : (((r7_relat_2(X1,X0) | ~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0)) & ((r6_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~r7_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : (((r7_relat_2(X1,X0) | (~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0))) & ((r6_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~r7_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    r7_relat_2(u1_orders_2(sK0),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f111,f48])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    r7_relat_2(u1_orders_2(sK0),sK1) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    v6_orders_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~v6_orders_2(sK1,sK0) | r7_relat_2(u1_orders_2(sK0),sK1) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(resolution,[],[f57,f50])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0) | r7_relat_2(u1_orders_2(X0),X1) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1)) & (r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~spl3_3 | spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f113,f120,f116])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    r6_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.21/0.49    inference(resolution,[],[f112,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r7_relat_2(X1,X0) | r6_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4689)------------------------------
% 0.21/0.49  % (4689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4689)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4689)Memory used [KB]: 5373
% 0.21/0.49  % (4689)Time elapsed: 0.067 s
% 0.21/0.49  % (4689)------------------------------
% 0.21/0.49  % (4689)------------------------------
% 0.21/0.49  % (4674)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (4679)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (4669)Success in time 0.132 s
%------------------------------------------------------------------------------
