%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t67_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:23 EDT 2019

% Result     : Theorem 34.65s
% Output     : Refutation 34.65s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 468 expanded)
%              Number of leaves         :   34 ( 166 expanded)
%              Depth                    :   22
%              Number of atoms          :  895 (1702 expanded)
%              Number of equality atoms :  105 ( 221 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13852,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f157,f164,f171,f178,f237,f245,f252,f259,f296,f315,f435,f444,f823,f3119,f3271,f4034,f4988,f13143,f13831,f13851])).

fof(f13851,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18
    | spl11_27
    | ~ spl11_308 ),
    inference(avatar_contradiction_clause,[],[f13850])).

fof(f13850,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_27
    | ~ spl11_308 ),
    inference(subsumption_resolution,[],[f13849,f244])).

fof(f244,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl11_12
  <=> m1_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f13849,plain,
    ( ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_27
    | ~ spl11_308 ),
    inference(subsumption_resolution,[],[f13848,f258])).

fof(f258,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl11_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f13848,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_18
    | ~ spl11_27
    | ~ spl11_308 ),
    inference(subsumption_resolution,[],[f13847,f400])).

fof(f400,plain,
    ( k1_xboole_0 != sK1
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl11_27
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f13847,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_18
    | ~ spl11_308 ),
    inference(subsumption_resolution,[],[f13846,f295])).

fof(f295,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl11_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f13846,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_308 ),
    inference(subsumption_resolution,[],[f13845,f236])).

fof(f236,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl11_11
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f13845,plain,
    ( r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_308 ),
    inference(superposition,[],[f13830,f201])).

fof(f201,plain,
    ( ! [X4,X5] :
        ( k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f200,f149])).

fof(f149,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f200,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f199,f170])).

fof(f170,plain,
    ( v5_orders_2(sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl11_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f199,plain,
    ( ! [X4,X5] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f198,f163])).

fof(f163,plain,
    ( v4_orders_2(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl11_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f198,plain,
    ( ! [X4,X5] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f181,f156])).

fof(f156,plain,
    ( v3_orders_2(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl11_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f181,plain,
    ( ! [X4,X5] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl11_8 ),
    inference(resolution,[],[f177,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',d15_orders_2)).

fof(f177,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl11_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f13830,plain,
    ( r1_tarski(k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)),sK1)
    | ~ spl11_308 ),
    inference(avatar_component_clause,[],[f13829])).

fof(f13829,plain,
    ( spl11_308
  <=> r1_tarski(k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_308])])).

fof(f13831,plain,
    ( spl11_308
    | ~ spl11_298 ),
    inference(avatar_split_clause,[],[f13823,f13141,f13829])).

fof(f13141,plain,
    ( spl11_298
  <=> k3_xboole_0(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2)))) = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_298])])).

fof(f13823,plain,
    ( r1_tarski(k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)),sK1)
    | ~ spl11_298 ),
    inference(superposition,[],[f103,f13142])).

fof(f13142,plain,
    ( k3_xboole_0(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2)))) = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl11_298 ),
    inference(avatar_component_clause,[],[f13141])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',t17_xboole_1)).

fof(f13143,plain,
    ( spl11_298
    | ~ spl11_142 ),
    inference(avatar_split_clause,[],[f4050,f4032,f13141])).

fof(f4032,plain,
    ( spl11_142
  <=> k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2))),sK1) = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_142])])).

fof(f4050,plain,
    ( k3_xboole_0(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2)))) = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl11_142 ),
    inference(superposition,[],[f4033,f104])).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',commutativity_k3_xboole_0)).

fof(f4033,plain,
    ( k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2))),sK1) = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl11_142 ),
    inference(avatar_component_clause,[],[f4032])).

fof(f4988,plain,
    ( spl11_66
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f4860,f313,f257,f985])).

fof(f985,plain,
    ( spl11_66
  <=> k3_xboole_0(k1_xboole_0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f313,plain,
    ( spl11_20
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f4860,plain,
    ( k3_xboole_0(k1_xboole_0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_xboole_0
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(resolution,[],[f3952,f101])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',existence_m1_subset_1)).

fof(f3952,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(k1_xboole_0,X3) = k1_xboole_0 )
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(superposition,[],[f3783,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',redefinition_k9_subset_1)).

fof(f3783,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X1) = k1_xboole_0
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(backward_demodulation,[],[f3781,f337])).

fof(f337,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X1)
    | ~ spl11_20 ),
    inference(resolution,[],[f314,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',commutativity_k9_subset_1)).

fof(f314,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f313])).

fof(f3781,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0) = k1_xboole_0
    | ~ spl11_16 ),
    inference(forward_demodulation,[],[f3754,f91])).

fof(f91,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',t2_boole)).

fof(f3754,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0)
    | ~ spl11_16 ),
    inference(superposition,[],[f3531,f91])).

fof(f3531,plain,
    ( ! [X2,X1] : k3_xboole_0(X2,k3_xboole_0(sK1,X1)) = k9_subset_1(u1_struct_0(sK0),X2,k3_xboole_0(sK1,X1))
    | ~ spl11_16 ),
    inference(superposition,[],[f3501,f104])).

fof(f3501,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,k3_xboole_0(X1,sK1))
    | ~ spl11_16 ),
    inference(backward_demodulation,[],[f3500,f274])).

fof(f274,plain,
    ( ! [X0,X1] : k9_subset_1(u1_struct_0(sK0),X0,k3_xboole_0(X1,sK1)) = k9_subset_1(u1_struct_0(sK0),k3_xboole_0(X1,sK1),X0)
    | ~ spl11_16 ),
    inference(resolution,[],[f271,f122])).

fof(f271,plain,
    ( ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_16 ),
    inference(forward_demodulation,[],[f270,f267])).

fof(f267,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f261,f258])).

fof(f261,plain,
    ( ! [X1] :
        ( k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_16 ),
    inference(superposition,[],[f260,f121])).

fof(f260,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl11_16 ),
    inference(resolution,[],[f258,f122])).

fof(f270,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f264,f258])).

fof(f264,plain,
    ( ! [X1] :
        ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_16 ),
    inference(superposition,[],[f120,f260])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',dt_k9_subset_1)).

fof(f3500,plain,
    ( ! [X17,X16] : k3_xboole_0(X16,k3_xboole_0(X17,sK1)) = k9_subset_1(u1_struct_0(sK0),k3_xboole_0(X17,sK1),X16)
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f3479,f271])).

fof(f3479,plain,
    ( ! [X17,X16] :
        ( k3_xboole_0(X16,k3_xboole_0(X17,sK1)) = k9_subset_1(u1_struct_0(sK0),k3_xboole_0(X17,sK1),X16)
        | ~ m1_subset_1(k3_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_16 ),
    inference(superposition,[],[f274,f121])).

fof(f4034,plain,
    ( spl11_142
    | spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18
    | spl11_27 ),
    inference(avatar_split_clause,[],[f3606,f399,f294,f257,f243,f176,f169,f162,f155,f148,f4032])).

fof(f3606,plain,
    ( k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2))),sK1) = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f3585,f258])).

fof(f3585,plain,
    ( k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2))),sK1) = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_27 ),
    inference(superposition,[],[f3291,f268])).

fof(f268,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1)
    | ~ spl11_16 ),
    inference(backward_demodulation,[],[f267,f260])).

fof(f3291,plain,
    ( ! [X4] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2))),X4) = k3_orders_2(sK0,X4,sK3(sK0,sK1,sK2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f670,f400])).

fof(f670,plain,
    ( ! [X4] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2))),X4) = k3_orders_2(sK0,X4,sK3(sK0,sK1,sK2))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f669,f295])).

fof(f669,plain,
    ( ! [X4] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2))),X4) = k3_orders_2(sK0,X4,sK3(sK0,sK1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f665,f258])).

fof(f665,plain,
    ( ! [X4] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1,sK2))),X4) = k3_orders_2(sK0,X4,sK3(sK0,sK1,sK2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12 ),
    inference(resolution,[],[f369,f244])).

fof(f369,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_2(X2,sK0,X1)
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,X1,X2))),X0) = k3_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f368,f149])).

fof(f368,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,X1,X2))),X0) = k3_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f367,f177])).

fof(f367,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,X1,X2))),X0) = k3_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f366,f170])).

fof(f366,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,X1,X2))),X0) = k3_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f365,f163])).

fof(f365,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,X1,X2))),X0) = k3_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f361,f156])).

fof(f361,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK0,X1,X2))),X0) = k3_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(resolution,[],[f193,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | v2_struct_0(X0)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)),X0) = k3_orders_2(sK0,X0,X1) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f192,f149])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)),X0) = k3_orders_2(sK0,X0,X1) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f191,f170])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)),X0) = k3_orders_2(sK0,X0,X1) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f190,f163])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)),X0) = k3_orders_2(sK0,X0,X1) )
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f179,f156])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)),X0) = k3_orders_2(sK0,X0,X1) )
    | ~ spl11_8 ),
    inference(resolution,[],[f177,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',d14_orders_2)).

fof(f3271,plain,
    ( spl11_61
    | ~ spl11_66 ),
    inference(avatar_contradiction_clause,[],[f3270])).

fof(f3270,plain,
    ( $false
    | ~ spl11_61
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f1004,f787])).

fof(f787,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl11_61 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl11_61
  <=> ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f1004,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl11_66 ),
    inference(superposition,[],[f103,f986])).

fof(f986,plain,
    ( k3_xboole_0(k1_xboole_0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_xboole_0
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f985])).

fof(f3119,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_30
    | spl11_33
    | ~ spl11_62 ),
    inference(avatar_contradiction_clause,[],[f3118])).

fof(f3118,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_30
    | ~ spl11_33
    | ~ spl11_62 ),
    inference(subsumption_resolution,[],[f3014,f822])).

fof(f822,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_62 ),
    inference(avatar_component_clause,[],[f821])).

fof(f821,plain,
    ( spl11_62
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f3014,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_30
    | ~ spl11_33 ),
    inference(backward_demodulation,[],[f3010,f443])).

fof(f443,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl11_33
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f3010,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f3008,f295])).

fof(f3008,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_20
    | ~ spl11_30 ),
    inference(resolution,[],[f347,f434])).

fof(f434,plain,
    ( m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl11_30
  <=> m1_orders_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f347,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,k1_xboole_0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f346,f149])).

fof(f346,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f345,f177])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f344,f170])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f343,f163])).

fof(f343,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl11_2
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f336,f156])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl11_20 ),
    inference(resolution,[],[f314,f135])).

fof(f135,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f823,plain,
    ( spl11_62
    | ~ spl11_60 ),
    inference(avatar_split_clause,[],[f801,f789,f821])).

fof(f789,plain,
    ( spl11_60
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f801,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_60 ),
    inference(resolution,[],[f790,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',t3_subset)).

fof(f790,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f789])).

fof(f444,plain,
    ( ~ spl11_33
    | spl11_15
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f407,f402,f250,f442])).

fof(f250,plain,
    ( spl11_15
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f402,plain,
    ( spl11_26
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f407,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_15
    | ~ spl11_26 ),
    inference(backward_demodulation,[],[f403,f251])).

fof(f251,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f250])).

fof(f403,plain,
    ( k1_xboole_0 = sK1
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f402])).

fof(f435,plain,
    ( spl11_30
    | ~ spl11_12
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f406,f402,f243,f433])).

fof(f406,plain,
    ( m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ spl11_12
    | ~ spl11_26 ),
    inference(backward_demodulation,[],[f403,f244])).

fof(f315,plain,
    ( spl11_20
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f282,f257,f313])).

fof(f282,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_16 ),
    inference(superposition,[],[f276,f91])).

fof(f276,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_16 ),
    inference(superposition,[],[f271,f104])).

fof(f296,plain,
    ( spl11_18
    | spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f289,f257,f243,f176,f169,f162,f155,f148,f294])).

fof(f289,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f286,f258])).

fof(f286,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_12 ),
    inference(resolution,[],[f205,f244])).

fof(f205,plain,
    ( ! [X6,X7] :
        ( ~ m1_orders_2(X7,sK0,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f204,f149])).

fof(f204,plain,
    ( ! [X6,X7] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X7,sK0,X6)
        | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f203,f170])).

fof(f203,plain,
    ( ! [X6,X7] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X7,sK0,X6)
        | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f202,f163])).

fof(f202,plain,
    ( ! [X6,X7] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X7,sK0,X6)
        | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f182,f156])).

fof(f182,plain,
    ( ! [X6,X7] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X7,sK0,X6)
        | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_8 ),
    inference(resolution,[],[f177,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',dt_m1_orders_2)).

fof(f259,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f84,f257])).

fof(f84,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_orders_2(X2,X0,X1)
               => r1_tarski(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t67_orders_2.p',t67_orders_2)).

fof(f252,plain,
    ( ~ spl11_15
    | spl11_11 ),
    inference(avatar_split_clause,[],[f238,f235,f250])).

fof(f238,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl11_11 ),
    inference(resolution,[],[f236,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f245,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f82,f243])).

fof(f82,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f237,plain,(
    ~ spl11_11 ),
    inference(avatar_split_clause,[],[f83,f235])).

fof(f83,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f178,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f89,f176])).

fof(f89,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f171,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f88,f169])).

fof(f88,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f164,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f87,f162])).

fof(f87,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f157,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f86,f155])).

fof(f86,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f150,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f85,f148])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
