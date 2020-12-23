%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1165+1.001 : TPTP v7.4.0. Released v7.4.0.
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
% Statistics : Number of formulae       :  151 ( 329 expanded)
%              Number of leaves         :   21 ( 125 expanded)
%              Depth                    :   22
%              Number of atoms          :  944 (1690 expanded)
%              Number of equality atoms :  109 ( 238 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f707,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f118,f127,f160,f173,f178,f187,f244,f405,f456,f698,f706])).

fof(f706,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8
    | spl6_45 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8
    | spl6_45 ),
    inference(subsumption_resolution,[],[f704,f126])).

fof(f126,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_8
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f704,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_45 ),
    inference(subsumption_resolution,[],[f703,f121])).

fof(f121,plain,
    ( k1_xboole_0 != sK1
    | spl6_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f703,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_45 ),
    inference(subsumption_resolution,[],[f702,f117])).

fof(f117,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f702,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_45 ),
    inference(duplicate_literal_removal,[],[f699])).

fof(f699,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_2(sK1,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_45 ),
    inference(resolution,[],[f697,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f100,f72])).

fof(f72,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

% (5908)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f100,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f99,f87])).

fof(f87,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f98,f82])).

fof(f82,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f94,f77])).

fof(f77,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f94,plain,
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
    | ~ spl6_5 ),
    inference(resolution,[],[f92,f43])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

fof(f92,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f697,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl6_45 ),
    inference(avatar_component_clause,[],[f695])).

fof(f695,plain,
    ( spl6_45
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f698,plain,
    ( ~ spl6_45
    | spl6_16
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f662,f453,f241,f695])).

fof(f241,plain,
    ( spl6_16
  <=> r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f453,plain,
    ( spl6_28
  <=> sK1 = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f662,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl6_16
    | ~ spl6_28 ),
    inference(superposition,[],[f313,f455])).

fof(f455,plain,
    ( sK1 = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f453])).

fof(f313,plain,
    ( ! [X1] : ~ r2_hidden(sK2(sK0,sK1,sK1),k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X1))
    | spl6_16 ),
    inference(resolution,[],[f247,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f247,plain,
    ( ! [X0] : ~ sP5(sK2(sK0,sK1,sK1),X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl6_16 ),
    inference(resolution,[],[f243,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f243,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f241])).

fof(f456,plain,
    ( spl6_28
    | ~ spl6_6
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f411,f402,f115,f453])).

fof(f402,plain,
    ( spl6_25
  <=> sK1 = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f411,plain,
    ( sK1 = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | ~ spl6_6
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f407,f117])).

fof(f407,plain,
    ( sK1 = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_25 ),
    inference(superposition,[],[f404,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f404,plain,
    ( sK1 = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f402])).

fof(f405,plain,
    ( spl6_25
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f291,f157,f124,f120,f115,f90,f85,f80,f75,f70,f402])).

fof(f157,plain,
    ( spl6_10
  <=> sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f291,plain,
    ( sK1 = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f289,f159])).

fof(f159,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f289,plain,
    ( k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f231,f117])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f230,f121])).

fof(f230,plain,
    ( ! [X0] :
        ( k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X0)
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f229,f117])).

fof(f229,plain,
    ( ! [X0] :
        ( k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( ! [X0] :
        ( k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f142,f126])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_2(X2,sK0,X1)
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f141,f72])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f140,f92])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X0,sK2(sK0,X1,X2)) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1,X2))),X0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f139,f87])).

fof(f139,plain,
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
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f138,f82])).

fof(f138,plain,
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
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f136,f77])).

fof(f136,plain,
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
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f109,f42])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f109,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f108,f72])).

fof(f108,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f107,f87])).

fof(f107,plain,
    ( ! [X4,X5] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f106,f82])).

fof(f106,plain,
    ( ! [X4,X5] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f96,f77])).

fof(f96,plain,
    ( ! [X4,X5] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_orders_2(sK0,X4,X5) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X5)),X4) )
    | ~ spl6_5 ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

fof(f244,plain,
    ( ~ spl6_16
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f218,f124,f120,f115,f90,f85,f80,f75,f70,f241])).

fof(f218,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f217,f121])).

fof(f217,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f216,f117])).

fof(f216,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f134,f126])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1)))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f133,f72])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f132,f92])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1))))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f131,f87])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0,X1))))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f130,f82])).

fof(f130,plain,
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
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f128,f77])).

fof(f128,plain,
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
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f113,f42])).

fof(f113,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f112,f72])).

fof(f112,plain,
    ( ! [X6] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f111,f87])).

fof(f111,plain,
    ( ! [X6] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f110,f82])).

fof(f110,plain,
    ( ! [X6] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f97,f77])).

fof(f97,plain,
    ( ! [X6] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X6))) )
    | ~ spl6_5 ),
    inference(resolution,[],[f92,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

fof(f187,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_11
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f185,f172])).

fof(f172,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_11
  <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f185,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f184,f72])).

fof(f184,plain,
    ( v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f183,f92])).

fof(f183,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f182,f87])).

fof(f182,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f181,f82])).

fof(f181,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f179,f77])).

fof(f179,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl6_12 ),
    inference(resolution,[],[f177,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
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
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f177,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f178,plain,
    ( spl6_12
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f163,f120,f115,f175])).

fof(f163,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(superposition,[],[f117,f122])).

fof(f122,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f173,plain,
    ( ~ spl6_11
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f167,f120,f170])).

fof(f167,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f166,f122])).

fof(f166,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f32,f122])).

fof(f32,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

fof(f160,plain,
    ( spl6_10
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f151,f124,f120,f115,f90,f85,f80,f75,f70,f157])).

fof(f151,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f150,f121])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f149,f117])).

fof(f149,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f105,f126])).

fof(f105,plain,
    ( ! [X2,X3] :
        ( ~ m1_orders_2(X3,sK0,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f104,f72])).

fof(f104,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_orders_2(X3,sK0,X2) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f103,f87])).

fof(f103,plain,
    ( ! [X2,X3] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_orders_2(X3,sK0,X2) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f102,f82])).

fof(f102,plain,
    ( ! [X2,X3] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | k3_orders_2(sK0,X2,sK2(sK0,X2,X3)) = X3
        | ~ m1_orders_2(X3,sK0,X2) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f95,f77])).

fof(f95,plain,
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
    | ~ spl6_5 ),
    inference(resolution,[],[f92,f44])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f127,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f31,f124,f120])).

fof(f31,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f118,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f33,f115])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f34,f70])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
