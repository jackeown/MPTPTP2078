%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 535 expanded)
%              Number of leaves         :   23 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  393 (3722 expanded)
%              Number of equality atoms :   36 (  82 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f606,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f122,f171,f268,f272,f305,f309,f349,f395,f454,f548])).

fof(f548,plain,
    ( ~ spl5_2
    | spl5_3
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | ~ spl5_2
    | spl5_3
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f230,f517,f519,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f519,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(superposition,[],[f224,f394])).

fof(f394,plain,
    ( sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl5_12
  <=> sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f224,plain,
    ( ! [X0] : r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f43,f219,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

% (26423)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f219,plain,
    ( ! [X0] : r2_hidden(k1_yellow_0(sK0,X0),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f49,f42,f112,f43,f85,f121,f218,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f218,plain,(
    ! [X0] : r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f217,f84])).

fof(f84,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f49,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f217,plain,(
    ! [X0] : r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f212,f120])).

fof(f120,plain,(
    ! [X0] : k1_yellow_0(sK0,X0) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f45,f46,f49,f47,f44,f85,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f212,plain,(
    ! [X0] : r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) ),
    inference(unit_resulting_resolution,[],[f49,f86,f76,f119,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_yellow_0(X0,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f119,plain,(
    ! [X0] : r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f45,f46,f49,f47,f44,f85,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f86,plain,(
    r1_yellow_0(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f47,f48,f44,f49,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f48,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f121,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f85,f84])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f49,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f112,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_2
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f42,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f517,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(superposition,[],[f219,f394])).

fof(f230,plain,
    ( sK1 != u1_struct_0(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl5_3
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

% (26444)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f454,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f406,f396,f77])).

fof(f77,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f396,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f43,f231])).

fof(f231,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f229])).

fof(f406,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f109,f231])).

fof(f109,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_1
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f395,plain,
    ( spl5_12
    | spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f390,f347,f229,f392])).

fof(f347,plain,
    ( spl5_11
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f390,plain,
    ( sK1 = u1_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,
    ( sK1 = u1_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))
    | ~ spl5_11 ),
    inference(resolution,[],[f367,f348])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f347])).

fof(f367,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(X0,sK1),X0)
        | sK1 = X0
        | sK2(X0,sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(X0,sK1))) )
    | ~ spl5_11 ),
    inference(resolution,[],[f362,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f362,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(X1,sK1),X1)
        | sK2(X1,sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(X1,sK1)))
        | sK1 = X1 )
    | ~ spl5_11 ),
    inference(resolution,[],[f354,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f354,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 )
    | ~ spl5_11 ),
    inference(resolution,[],[f348,f102])).

fof(f102,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f43,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f349,plain,
    ( spl5_11
    | ~ spl5_6
    | ~ spl5_8
    | spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f82,f298,f257,f261,f253,f347])).

fof(f253,plain,
    ( spl5_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f261,plain,
    ( spl5_8
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f257,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f298,plain,
    ( spl5_10
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f82,plain,(
    ! [X1] :
      ( ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 ) ),
    inference(resolution,[],[f46,f71])).

fof(f309,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f44,f259])).

fof(f259,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f257])).

fof(f305,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f45,f300])).

fof(f300,plain,
    ( ~ v3_orders_2(sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f298])).

fof(f272,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f47,f263])).

fof(f263,plain,
    ( ~ v5_orders_2(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f261])).

fof(f268,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f49,f255])).

fof(f255,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f253])).

fof(f171,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f40,f113,f139,f67])).

% (26431)Refutation not found, incomplete strategy% (26431)------------------------------
% (26431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26431)Termination reason: Refutation not found, incomplete strategy

% (26431)Memory used [KB]: 10746
% (26431)Time elapsed: 0.135 s
% (26431)------------------------------
% (26431)------------------------------
fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f139,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl5_1 ),
    inference(backward_demodulation,[],[f121,f123])).

fof(f123,plain,
    ( sK1 = u1_struct_0(sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f43,f108,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f113,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f40,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f39,f111,f107])).

fof(f39,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f114,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f38,f111,f107])).

fof(f38,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (26426)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (26442)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (26425)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (26436)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (26428)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (26443)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (26431)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (26438)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (26435)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (26427)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (26426)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (26446)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (26441)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (26424)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (26432)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (26422)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (26434)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (26433)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (26430)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (26452)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f606,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f114,f122,f171,f268,f272,f305,f309,f349,f395,f454,f548])).
% 0.22/0.54  fof(f548,plain,(
% 0.22/0.54    ~spl5_2 | spl5_3 | ~spl5_12),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f546])).
% 0.22/0.54  fof(f546,plain,(
% 0.22/0.54    $false | (~spl5_2 | spl5_3 | ~spl5_12)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f230,f517,f519,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.54  fof(f519,plain,(
% 0.22/0.54    r2_hidden(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_12)),
% 0.22/0.54    inference(superposition,[],[f224,f394])).
% 0.22/0.54  fof(f394,plain,(
% 0.22/0.54    sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) | ~spl5_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f392])).
% 0.22/0.54  fof(f392,plain,(
% 0.22/0.54    spl5_12 <=> sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) ) | ~spl5_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f43,f219,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.54  % (26423)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f219,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_yellow_0(sK0,X0),sK1)) ) | ~spl5_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f49,f42,f112,f43,f85,f121,f218,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f217,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f49,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    ( ! [X0] : (r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f212,f120])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ( ! [X0] : (k1_yellow_0(sK0,X0) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f45,f46,f49,f47,f44,f85,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f16])).
% 0.22/0.54  fof(f16,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    v5_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    v4_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    v3_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    ( ! [X0] : (r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))))) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f49,f86,f76,f119,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_tarski(X1,X2) | ~r1_yellow_0(X0,X1) | ~r1_yellow_0(X0,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ( ! [X0] : (r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f45,f46,f49,f47,f44,f85,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_yellow_0(X0,k5_waybel_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    r1_yellow_0(sK0,k1_xboole_0)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f47,f48,f44,f49,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    v1_yellow_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.22/0.54    inference(superposition,[],[f85,f84])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f49,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f111])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    spl5_2 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    v13_waybel_0(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    l1_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f517,plain,(
% 0.22/0.54    r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | (~spl5_2 | ~spl5_12)),
% 0.22/0.54    inference(superposition,[],[f219,f394])).
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    sK1 != u1_struct_0(sK0) | spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f229])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    spl5_3 <=> sK1 = u1_struct_0(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  % (26444)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  fof(f454,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f448])).
% 0.22/0.54  fof(f448,plain,(
% 0.22/0.54    $false | (~spl5_1 | ~spl5_3)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f406,f396,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.54  fof(f396,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl5_3),
% 0.22/0.54    inference(backward_demodulation,[],[f43,f231])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    sK1 = u1_struct_0(sK0) | ~spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f229])).
% 0.22/0.54  fof(f406,plain,(
% 0.22/0.54    v1_subset_1(sK1,sK1) | (~spl5_1 | ~spl5_3)),
% 0.22/0.54    inference(backward_demodulation,[],[f109,f231])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    spl5_1 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f395,plain,(
% 0.22/0.54    spl5_12 | spl5_3 | ~spl5_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f390,f347,f229,f392])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    spl5_11 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.54  fof(f390,plain,(
% 0.22/0.54    sK1 = u1_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) | ~spl5_11),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f389])).
% 0.22/0.54  fof(f389,plain,(
% 0.22/0.54    sK1 = u1_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) | ~spl5_11),
% 0.22/0.54    inference(resolution,[],[f367,f348])).
% 0.22/0.54  fof(f348,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1) ) | ~spl5_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f347])).
% 0.22/0.54  fof(f367,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK2(X0,sK1),X0) | sK1 = X0 | sK2(X0,sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(X0,sK1)))) ) | ~spl5_11),
% 0.22/0.54    inference(resolution,[],[f362,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.54  fof(f362,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(sK2(X1,sK1),X1) | sK2(X1,sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(X1,sK1))) | sK1 = X1) ) | ~spl5_11),
% 0.22/0.54    inference(resolution,[],[f354,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1) ) | ~spl5_11),
% 0.22/0.54    inference(resolution,[],[f348,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X1] : (m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f43,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.54  fof(f349,plain,(
% 0.22/0.54    spl5_11 | ~spl5_6 | ~spl5_8 | spl5_7 | ~spl5_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f82,f298,f257,f261,f253,f347])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    spl5_6 <=> l1_orders_2(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    spl5_8 <=> v5_orders_2(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    spl5_7 <=> v2_struct_0(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.54  fof(f298,plain,(
% 0.22/0.54    spl5_10 <=> v3_orders_2(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X1] : (~v3_orders_2(sK0) | v2_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1) )),
% 0.22/0.54    inference(resolution,[],[f46,f71])).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    ~spl5_7),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f306])).
% 0.22/0.54  fof(f306,plain,(
% 0.22/0.54    $false | ~spl5_7),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f44,f259])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    v2_struct_0(sK0) | ~spl5_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f257])).
% 0.22/0.54  fof(f305,plain,(
% 0.22/0.54    spl5_10),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f302])).
% 0.22/0.54  fof(f302,plain,(
% 0.22/0.54    $false | spl5_10),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f45,f300])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    ~v3_orders_2(sK0) | spl5_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f298])).
% 0.22/0.54  fof(f272,plain,(
% 0.22/0.54    spl5_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f269])).
% 0.22/0.54  fof(f269,plain,(
% 0.22/0.54    $false | spl5_8),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f47,f263])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    ~v5_orders_2(sK0) | spl5_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f261])).
% 0.22/0.54  fof(f268,plain,(
% 0.22/0.54    spl5_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f265])).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    $false | spl5_6),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f49,f255])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    ~l1_orders_2(sK0) | spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f253])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    spl5_1 | spl5_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    $false | (spl5_1 | spl5_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f40,f113,f139,f67])).
% 0.22/0.55  % (26431)Refutation not found, incomplete strategy% (26431)------------------------------
% 0.22/0.55  % (26431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26431)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26431)Memory used [KB]: 10746
% 0.22/0.55  % (26431)Time elapsed: 0.135 s
% 0.22/0.55  % (26431)------------------------------
% 0.22/0.55  % (26431)------------------------------
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    m1_subset_1(k3_yellow_0(sK0),sK1) | spl5_1),
% 0.22/0.55    inference(backward_demodulation,[],[f121,f123])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    sK1 = u1_struct_0(sK0) | spl5_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f43,f108,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl5_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f107])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl5_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f111])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ~v1_xboole_0(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ~spl5_1 | spl5_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f39,f111,f107])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    spl5_1 | ~spl5_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f38,f111,f107])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (26426)------------------------------
% 0.22/0.55  % (26426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26426)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (26426)Memory used [KB]: 6396
% 0.22/0.55  % (26426)Time elapsed: 0.103 s
% 0.22/0.55  % (26426)------------------------------
% 0.22/0.55  % (26426)------------------------------
% 0.22/0.55  % (26419)Success in time 0.188 s
%------------------------------------------------------------------------------
