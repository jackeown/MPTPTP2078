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
% DateTime   : Thu Dec  3 13:09:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 163 expanded)
%              Number of leaves         :    8 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  247 (1097 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f46,f78,f91,f103,f111])).

fof(f111,plain,
    ( ~ spl4_1
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f105,f15])).

fof(f15,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r2_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X2) )
                        | ( r1_orders_2(X0,X2,X3)
                          & r2_orders_2(X0,X1,X2) ) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

fof(f105,plain,
    ( r2_orders_2(sK0,sK1,sK3)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f30,f102])).

% (6042)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f102,plain,
    ( sK1 = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_6
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f30,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f103,plain,
    ( spl4_2
    | spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f98,f37,f100,f32])).

fof(f32,plain,
    ( spl4_2
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f37,plain,
    ( spl4_3
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f98,plain,
    ( sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f97,f20])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,
    ( ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f96,f16])).

fof(f16,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f96,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f65,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f39,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f39,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f91,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f89,plain,
    ( ~ r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f86,f16])).

fof(f86,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f52,f34])).

fof(f34,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f51,f18])).

fof(f18,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X0)
      | ~ r2_orders_2(sK0,X0,sK3)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f50,f14])).

fof(f14,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X0)
      | ~ r2_orders_2(sK0,X0,sK3)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f49,f17])).

fof(f49,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X0)
      | ~ r2_orders_2(sK0,X0,sK3)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f48,f20])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X0)
      | ~ r2_orders_2(sK0,X0,sK3)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f47,f19])).

fof(f19,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X0)
      | ~ r2_orders_2(sK0,X0,sK3)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f15,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X3)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r2_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

fof(f78,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f76,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f15,f70])).

fof(f70,plain,
    ( sK2 = sK3
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f69,f29])).

fof(f29,plain,
    ( ~ r2_orders_2(sK0,sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f69,plain,
    ( sK2 = sK3
    | r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f68,f20])).

fof(f68,plain,
    ( ~ l1_orders_2(sK0)
    | sK2 = sK3
    | r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f67,f14])).

fof(f67,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK2 = sK3
    | r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f66,f16])).

fof(f66,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK2 = sK3
    | r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f44,f23])).

fof(f44,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_4
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f46,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f10,f42,f37])).

fof(f10,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,
    ( spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f11,f42,f28])).

fof(f11,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f12,f32,f37])).

fof(f12,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f13,f32,f28])).

fof(f13,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.47  % (6038)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (6047)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (6034)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (6034)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (6048)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (6052)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (6041)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (6039)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (6050)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (6040)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (6046)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (6033)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f35,f40,f45,f46,f78,f91,f103,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    $false | (~spl4_1 | ~spl4_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f105,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ~r2_orders_2(sK0,sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    r2_orders_2(sK0,sK1,sK3) | (~spl4_1 | ~spl4_6)),
% 0.21/0.49    inference(backward_demodulation,[],[f30,f102])).
% 0.21/0.49  % (6042)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    sK1 = sK2 | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl4_6 <=> sK1 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    r2_orders_2(sK0,sK2,sK3) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    spl4_1 <=> r2_orders_2(sK0,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl4_2 | spl4_6 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f37,f100,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    spl4_2 <=> r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl4_3 <=> r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    sK1 = sK2 | r2_orders_2(sK0,sK1,sK2) | ~spl4_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    l1_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | sK1 = sK2 | r2_orders_2(sK0,sK1,sK2) | ~spl4_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK2 | r2_orders_2(sK0,sK1,sK2) | ~spl4_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f65,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK2 | r2_orders_2(sK0,sK1,sK2) | ~spl4_3),
% 0.21/0.49    inference(resolution,[],[f39,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2 | r2_orders_2(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    r1_orders_2(sK0,sK1,sK2) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f37])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    $false | (~spl4_1 | ~spl4_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f30])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~r2_orders_2(sK0,sK2,sK3) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f16])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK2,sK3) | ~spl4_2),
% 0.21/0.49    inference(resolution,[],[f52,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    r2_orders_2(sK0,sK1,sK2) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f32])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,sK3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f51,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    v4_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0) | ~r2_orders_2(sK0,X0,sK3) | ~v4_orders_2(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f50,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0) | ~r2_orders_2(sK0,X0,sK3) | ~v4_orders_2(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f49,f17])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0) | ~r2_orders_2(sK0,X0,sK3) | ~v4_orders_2(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f48,f20])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0) | ~r2_orders_2(sK0,X0,sK3) | ~v4_orders_2(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f47,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v5_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0) | ~r2_orders_2(sK0,X0,sK3) | ~v4_orders_2(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f15,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X3) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X3) | ~v4_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | (~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    $false | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f76,f34])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~r2_orders_2(sK0,sK1,sK2) | (spl4_1 | ~spl4_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f15,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    sK2 = sK3 | (spl4_1 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f69,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ~r2_orders_2(sK0,sK2,sK3) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f28])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    sK2 = sK3 | r2_orders_2(sK0,sK2,sK3) | ~spl4_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f68,f20])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | sK2 = sK3 | r2_orders_2(sK0,sK2,sK3) | ~spl4_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f67,f14])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK2 = sK3 | r2_orders_2(sK0,sK2,sK3) | ~spl4_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f66,f16])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK2 = sK3 | r2_orders_2(sK0,sK2,sK3) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f44,f23])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    r1_orders_2(sK0,sK2,sK3) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl4_4 <=> r1_orders_2(sK0,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl4_3 | spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f10,f42,f37])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    r1_orders_2(sK0,sK2,sK3) | r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl4_1 | spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f11,f42,f28])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    r1_orders_2(sK0,sK2,sK3) | r2_orders_2(sK0,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl4_3 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f12,f32,f37])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    r2_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl4_1 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f13,f32,f28])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    r2_orders_2(sK0,sK1,sK2) | r2_orders_2(sK0,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (6034)------------------------------
% 0.21/0.49  % (6034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6034)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (6034)Memory used [KB]: 10618
% 0.21/0.49  % (6034)Time elapsed: 0.070 s
% 0.21/0.49  % (6034)------------------------------
% 0.21/0.49  % (6034)------------------------------
% 0.21/0.49  % (6032)Success in time 0.135 s
%------------------------------------------------------------------------------
