%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1165+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 342 expanded)
%              Number of leaves         :   24 ( 128 expanded)
%              Depth                    :   22
%              Number of atoms          :  957 (1709 expanded)
%              Number of equality atoms :  113 ( 243 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f991,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f107,f124,f171,f200,f227,f258,f359,f575,f830,f982,f990])).

fof(f990,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f989])).

fof(f989,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9
    | spl5_20 ),
    inference(subsumption_resolution,[],[f988,f123])).

fof(f123,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_9
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f988,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | spl5_20 ),
    inference(subsumption_resolution,[],[f987,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK1
    | spl5_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f987,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_20 ),
    inference(subsumption_resolution,[],[f986,f106])).

fof(f106,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f986,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_20 ),
    inference(duplicate_literal_removal,[],[f983])).

fof(f983,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_2(sK1,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_20 ),
    inference(resolution,[],[f981,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f89,f61])).

fof(f61,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f88,f76])).

fof(f76,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f87,f71])).

fof(f71,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f83,f66])).

fof(f66,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f81,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f81,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f981,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f979])).

fof(f979,plain,
    ( spl5_20
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f982,plain,
    ( ~ spl5_20
    | spl5_15
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f963,f827,f356,f979])).

fof(f356,plain,
    ( spl5_15
  <=> r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f827,plain,
    ( spl5_18
  <=> sK1 = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f963,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl5_15
    | ~ spl5_18 ),
    inference(superposition,[],[f471,f829])).

fof(f829,plain,
    ( sK1 = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f827])).

fof(f471,plain,
    ( ! [X1] : ~ r2_hidden(sK2(sK0,sK1,sK1),k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X1))
    | spl5_15 ),
    inference(resolution,[],[f360,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f360,plain,
    ( ! [X0] : ~ sP4(sK2(sK0,sK1,sK1),X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl5_15 ),
    inference(resolution,[],[f358,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f358,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f356])).

fof(f830,plain,
    ( spl5_18
    | ~ spl5_6
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f588,f572,f104,f827])).

fof(f572,plain,
    ( spl5_17
  <=> sK1 = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f588,plain,
    ( sK1 = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | ~ spl5_6
    | ~ spl5_17 ),
    inference(superposition,[],[f574,f108])).

fof(f108,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f106,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f574,plain,
    ( sK1 = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f572])).

fof(f575,plain,
    ( spl5_17
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f376,f197,f121,f117,f104,f79,f74,f69,f64,f59,f572])).

fof(f197,plain,
    ( spl5_12
  <=> sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f376,plain,
    ( sK1 = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f371,f199])).

fof(f199,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f197])).

fof(f371,plain,
    ( k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f266,f106])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f265,f118])).

fof(f265,plain,
    ( ! [X0] :
        ( k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X0)
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f264,f106])).

fof(f264,plain,
    ( ! [X0] :
        ( k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( ! [X0] :
        ( k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(resolution,[],[f123,f155])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_2(X2,sK0,X1)
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f154,f61])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f153,f81])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f152,f76])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f151,f71])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f150,f66])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f98,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | v2_struct_0(X0)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f97,f61])).

fof(f97,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f96,f76])).

fof(f96,plain,
    ( ! [X4,X5] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f95,f71])).

fof(f95,plain,
    ( ! [X4,X5] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f85,f66])).

fof(f85,plain,
    ( ! [X4,X5] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | ~ spl5_5 ),
    inference(resolution,[],[f81,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
             => k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_orders_2)).

fof(f359,plain,
    ( ~ spl5_15
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f268,f121,f117,f104,f79,f74,f69,f64,f59,f356])).

fof(f268,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f267,f118])).

fof(f267,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f263,f106])).

fof(f263,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(resolution,[],[f123,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1)))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f139,f61])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f138,f81])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1))))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f137,f76])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1))))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f136,f71])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1))))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f135,f66])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1))))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f102,f33])).

fof(f102,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f101,f61])).

fof(f101,plain,
    ( ! [X6] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f100,f76])).

fof(f100,plain,
    ( ! [X6] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f99,f71])).

fof(f99,plain,
    ( ! [X6] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f86,f66])).

fof(f86,plain,
    ( ! [X6] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | ~ spl5_5 ),
    inference(resolution,[],[f81,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(f258,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f181,f226])).

fof(f226,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl5_13
  <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f181,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f180,f61])).

fof(f180,plain,
    ( v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f179,f81])).

fof(f179,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f178,f76])).

fof(f178,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f177,f71])).

fof(f177,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f172,f66])).

fof(f172,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_11 ),
    inference(resolution,[],[f170,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X2
      | m1_orders_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | k1_xboole_0 != X2
      | m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f170,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f227,plain,
    ( ~ spl5_13
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f221,f117,f224])).

fof(f221,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f220,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f220,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f23,f119])).

fof(f23,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k1_xboole_0 = X1
                  & ~ m1_orders_2(X1,X0,X1) )
              & ~ ( m1_orders_2(X1,X0,X1)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

fof(f200,plain,
    ( spl5_12
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f159,f121,f117,f104,f79,f74,f69,f64,f59,f197])).

fof(f159,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f158,f118])).

fof(f158,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f157,f106])).

fof(f157,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(resolution,[],[f94,f123])).

fof(f94,plain,
    ( ! [X2,X3] :
        ( ~ m1_orders_2(X3,sK0,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f93,f61])).

fof(f93,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_orders_2(X3,sK0,X2) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f92,f76])).

fof(f92,plain,
    ( ! [X2,X3] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_orders_2(X3,sK0,X2) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f91,f71])).

fof(f91,plain,
    ( ! [X2,X3] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_orders_2(X3,sK0,X2) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f84,f66])).

fof(f84,plain,
    ( ! [X2,X3] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_orders_2(X3,sK0,X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f81,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f171,plain,
    ( spl5_11
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f164,f104,f168])).

fof(f164,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(superposition,[],[f130,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f130,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(superposition,[],[f126,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f126,plain,
    ( ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f109,f108])).

fof(f109,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f124,plain,
    ( spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f22,f121,f117])).

fof(f22,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f107,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f24,f104])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
