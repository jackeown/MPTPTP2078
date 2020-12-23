%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1575+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 190 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  347 ( 649 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f106,f133,f142,f147,f151,f153,f156])).

fof(f156,plain,
    ( ~ spl5_2
    | spl5_3
    | spl5_6
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl5_2
    | spl5_3
    | spl5_6
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f121,f145])).

fof(f145,plain,
    ( r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_11
  <=> r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f121,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0)))
    | ~ spl5_2
    | spl5_3
    | spl5_6 ),
    inference(subsumption_resolution,[],[f120,f64])).

fof(f64,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f53,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f120,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1(sK0)),u1_struct_0(sK0))
    | ~ spl5_2
    | spl5_3
    | spl5_6 ),
    inference(resolution,[],[f105,f83])).

fof(f83,plain,
    ( ! [X5] :
        ( r2_lattice3(sK0,sK1(sK0),sK3(sK0,X5))
        | ~ r2_lattice3(sK0,sK1(sK0),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f67,f58])).

fof(f58,plain,
    ( ~ v3_lattice3(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_3
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f67,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1(sK0),X5)
        | r2_lattice3(sK0,sK1(sK0),sK3(sK0,X5))
        | v3_lattice3(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK1(X0),X2)
      | r2_lattice3(X0,sK1(X0),sK3(X0,X2))
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_lattice3)).

fof(f105,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),sK3(sK0,k1_yellow_0(sK0,sK1(sK0))))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_6
  <=> r2_lattice3(sK0,sK1(sK0),sK3(sK0,k1_yellow_0(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f153,plain,
    ( ~ spl5_2
    | ~ spl5_5
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5
    | spl5_11 ),
    inference(subsumption_resolution,[],[f148,f100])).

fof(f100,plain,
    ( r1_yellow_0(sK0,sK1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_5
  <=> r1_yellow_0(sK0,sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f148,plain,
    ( ~ r1_yellow_0(sK0,sK1(sK0))
    | ~ spl5_2
    | spl5_11 ),
    inference(resolution,[],[f146,f72])).

fof(f72,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2))
        | ~ r1_yellow_0(sK0,X2) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f70,f53])).

fof(f70,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f146,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f151,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f149,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f149,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0))
    | spl5_10 ),
    inference(resolution,[],[f141,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f141,plain,
    ( ~ m1_subset_1(k3_xboole_0(u1_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_10
  <=> m1_subset_1(k3_xboole_0(u1_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f147,plain,
    ( ~ spl5_11
    | ~ spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f118,f95,f56,f51,f144])).

fof(f95,plain,
    ( spl5_4
  <=> m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f118,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0)))
    | ~ spl5_2
    | spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f117,f58])).

fof(f117,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0)))
    | v3_lattice3(sK0)
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f116,f53])).

fof(f116,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0)))
    | ~ l1_orders_2(sK0)
    | v3_lattice3(sK0)
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f115,f64])).

fof(f115,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1(sK0)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,sK1(sK0)))
    | ~ l1_orders_2(sK0)
    | v3_lattice3(sK0)
    | spl5_4 ),
    inference(resolution,[],[f97,f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( m1_subset_1(sK3(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK1(X0),X2)
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,
    ( ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1(sK0))),u1_struct_0(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f142,plain,
    ( ~ spl5_10
    | spl5_9 ),
    inference(avatar_split_clause,[],[f136,f130,f139])).

fof(f130,plain,
    ( spl5_9
  <=> r1_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f136,plain,
    ( ~ m1_subset_1(k3_xboole_0(u1_struct_0(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_9 ),
    inference(resolution,[],[f132,f19])).

fof(f19,plain,(
    ! [X1] :
      ( r1_yellow_0(sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v3_lattice3(X0)
      & ! [X1] :
          ( r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v3_lattice3(X0)
      & ! [X1] :
          ( r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_yellow_0(X0,X1) )
         => v3_lattice3(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
       => v3_lattice3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_yellow_0)).

fof(f132,plain,
    ( ~ r1_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),sK1(sK0)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( ~ spl5_9
    | spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f109,f99,f51,f46,f130])).

fof(f46,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f109,plain,
    ( ~ r1_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),sK1(sK0)))
    | spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(forward_demodulation,[],[f107,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f107,plain,
    ( ~ r1_yellow_0(sK0,k3_xboole_0(sK1(sK0),u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(resolution,[],[f101,f76])).

fof(f76,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK0,X2)
        | ~ r1_yellow_0(sK0,k3_xboole_0(X2,u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f62,f53])).

fof(f62,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,k3_xboole_0(X2,u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X2) )
    | spl5_1 ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X1)
           => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
           => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_yellow_0)).

fof(f48,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f101,plain,
    ( ~ r1_yellow_0(sK0,sK1(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f89,f56,f51,f103,f99,f95])).

fof(f89,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),sK3(sK0,k1_yellow_0(sK0,sK1(sK0))))
    | ~ r1_yellow_0(sK0,sK1(sK0))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1(sK0))),u1_struct_0(sK0))
    | ~ spl5_2
    | spl5_3 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ~ r2_lattice3(sK0,sK1(sK0),sK3(sK0,k1_yellow_0(sK0,sK1(sK0))))
    | ~ r1_yellow_0(sK0,sK1(sK0))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1(sK0))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1(sK0))
    | ~ spl5_2
    | spl5_3 ),
    inference(resolution,[],[f85,f72])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,X0))
        | ~ r2_lattice3(sK0,X0,sK3(sK0,k1_yellow_0(sK0,X0)))
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,X0)),u1_struct_0(sK0)) )
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f84,f64])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,X0)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK3(sK0,k1_yellow_0(sK0,X0)))
        | ~ r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1(sK0),k1_yellow_0(sK0,X0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl5_2
    | spl5_3 ),
    inference(resolution,[],[f71,f80])).

fof(f80,plain,
    ( ! [X6] :
        ( ~ r1_orders_2(sK0,X6,sK3(sK0,X6))
        | ~ r2_lattice3(sK0,sK1(sK0),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f68,f58])).

fof(f68,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1(sK0),X6)
        | ~ r1_orders_2(sK0,X6,sK3(sK0,X6))
        | v3_lattice3(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK1(X0),X2)
      | ~ r1_orders_2(X0,X2,sK3(X0,X2))
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f69,f53])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ~ v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
